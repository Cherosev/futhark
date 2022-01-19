{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Futhark.AD.Rev.Reduce
  ( diffReduce,
    diffMinMaxReduce,
    diffMult,
  )
where

import Control.Monad
import Futhark.AD.Rev.Monad
import Futhark.Analysis.PrimExp.Convert
import Futhark.Builder
import Futhark.IR.SOACS
import Futhark.Tools
import Futhark.Transform.Rename

eReverse :: MonadBuilder m => VName -> m VName
eReverse arr = do
  arr_t <- lookupType arr
  let w = arraySize 0 arr_t
  start <-
    letSubExp "rev_start" $
      BasicOp $ BinOp (Sub Int64 OverflowUndef) w (intConst Int64 1)
  let stride = intConst Int64 (-1)
      slice = fullSlice arr_t [DimSlice start w stride]
  letExp (baseString arr <> "_rev") $ BasicOp $ Index arr slice

eRotate :: MonadBuilder m => [SubExp] -> VName -> m VName
eRotate rots arr = letExp (baseString arr <> "_rot") $ BasicOp $ Rotate rots arr

scanExc ::
  (MonadBuilder m, Rep m ~ SOACS) =>
  String ->
  Scan SOACS ->
  [VName] ->
  m [VName]
scanExc desc scan arrs = do
  w <- arraysSize 0 <$> mapM lookupType arrs
  form <- scanSOAC [scan]
  res_incl <- letTupExp (desc <> "_incl") $ Op $ Screma w arrs form
  res_incl_rot <- mapM (eRotate [intConst Int64 (-1)]) res_incl

  iota <-
    letExp "iota" . BasicOp $
      Iota w (intConst Int64 0) (intConst Int64 1) Int64

  iparam <- newParam "iota_param" $ Prim int64
  vparams <- mapM (newParam "vp") ts
  let params = iparam : vparams

  body <- runBodyBuilder . localScope (scopeOfLParams params) $ do
    let first_elem =
          eCmpOp
            (CmpEq int64)
            (eSubExp (Var (paramName iparam)))
            (eSubExp (intConst Int64 0))
    eBody
      [ eIf
          first_elem
          (resultBodyM nes)
          (resultBodyM $ map (Var . paramName) vparams)
      ]

  let lam = Lambda params body ts
  letTupExp desc $ Op $ Screma w (iota : res_incl_rot) (mapSOAC lam)
  where
    nes = scanNeutral scan
    ts = lambdaReturnType $ scanLambda scan

mkF :: Lambda -> ADM ([VName], Lambda)
mkF lam = do
  lam_l <- renameLambda lam
  lam_r <- renameLambda lam
  let q = length $ lambdaReturnType lam
      (lps, aps) = splitAt q $ lambdaParams lam_l
      (ips, rps) = splitAt q $ lambdaParams lam_r
  lam' <- mkLambda (lps <> aps <> rps) $ do
    lam_l_res <- bodyBind $ lambdaBody lam_l
    forM_ (zip ips lam_l_res) $ \(ip, SubExpRes cs se) ->
      certifying cs $ letBindNames [paramName ip] $ BasicOp $ SubExp se
    bodyBind $ lambdaBody lam_r
  pure (map paramName aps, lam')

diffReduce :: VjpOps -> [VName] -> SubExp -> [VName] -> Reduce SOACS -> ADM ()
diffReduce _ops [adj] w [a] red
  | Just [(op, _, _, _)] <- lamIsBinOp $ redLambda red,
    isAdd op = do
    adj_rep <-
      letExp (baseString adj <> "_rep") $
        BasicOp $ Replicate (Shape [w]) $ Var adj
    void $ updateAdj a adj_rep
  where
    isAdd FAdd {} = True
    isAdd Add {} = True
    isAdd _ = False
--
-- Differentiating a general single reduce:
--    let y = reduce \odot ne as
-- Forward sweep:
--    let ls = scan_exc \odot  ne as
--    let rs = scan_exc \odot' ne (reverse as)
-- Reverse sweep:
--    let as_c = map3 (f_bar y_bar) ls as (reverse rs)
-- where
--   x \odot' y = y \odot x
--   y_bar is the adjoint of the result y
--   f l_i a_i r_i = l_i \odot a_i \odot r_i
--   f_bar = the reverse diff of f with respect to a_i under the adjoint y_bar
-- The plan is to create
--   one scanomap SOAC which computes ls and rs
--   another map which computes as_c
--
diffReduce ops pat_adj n as red = do
  let (lam0, ne) = (redLambda red, redNeutral red)
  let alphas = lambdaReturnType lam0
  lam <- renameLambda lam0
  lam' <- renameLambda lam0 {lambdaParams = flipParams $ lambdaParams lam0}
  par_i <- newParam "i" $ Prim int64
  -- phase1: build the scanomap soac
  g_bdy <- mkFusedMapBody par_i ne alphas
  let g_lam = Lambda [par_i] g_bdy (alphas ++ alphas)
  (r_scan, scan_stms) <- runBuilderT' $ do
    iota <- letExp "iota" $ BasicOp $ Iota n se0 se1 Int64
    letTupExp "adj_ctrb_scan" $
      Op $
        Screma n [iota] $ ScremaForm [Scan lam ne, Scan lam' ne] [] g_lam
  addStms scan_stms
  let (ls_arr, rs_arr) = splitAt (length ne) r_scan
  -- phase2: build the following map:
  (as_params, f) <- mkF $ redLambda red
  f_adj <- vjpLambda ops (map adjFromVar pat_adj) as_params f
  --
  par_i' <- newParam "i" $ Prim int64
  let i' = paramName par_i'
      f_adj_params = lambdaParams f_adj
      (ls_as_ps, rs_ps) = splitAt (2 * length ne) f_adj_params
      scp_params = par_i' : ls_as_ps ++ zipWith (Param mempty) pat_adj alphas
  f_adj_body <- runBodyBuilder . localScope (scopeOfLParams scp_params) $ do
    nmim1 <- letSubExp "n_i_1" =<< toExp (pe64 n - (le64 i' + pe64 se1))
    let idx_stms = map (mkIdxStm nmim1) $ zip3 alphas rs_arr $ map paramName rs_ps
    addStms (stmsFromList idx_stms)
    pure $ lambdaBody f_adj
  let map_lam = Lambda (par_i' : ls_as_ps) f_adj_body alphas
  (as_adj, map_stms) <- runBuilderT' $ do
    iota <- letExp "iota" $ BasicOp $ Iota n se0 se1 Int64
    letTupExp "adj_ctrb_scan" $
      Op $
        Screma n (iota : ls_arr ++ as) $
          ScremaForm [] [] map_lam
  addStms map_stms
  -- finally add contributions to the adjoint of as
  zipWithM_ updateAdj as as_adj
  where
    se0 = intConst Int64 0
    se1 = intConst Int64 1
    addFixIdx2FullSlice idx t =
      let full_dims = unSlice $ fullSlice t []
       in Slice $ DimFix idx : full_dims
    flipParams ps = uncurry (flip (++)) $ splitAt (length ps `div` 2) ps
    mkFusedMapBody par_i ne alphas = do
      let i = paramName par_i
      runBodyBuilder . localScope (scopeOfLParams [par_i]) $
        eBody
          [ eIf
              (toExp $ le64 i .>. pe64 se0)
              ( do
                  ((rs1, rs2), stms) <- runBuilderT' . localScope (scopeOfLParams [par_i]) $ do
                    im1 <- letSubExp "i_1" =<< toExp (le64 i - pe64 se1)
                    nmi <- letSubExp "n_i" =<< toExp (pe64 n - le64 i)
                    tmp <- forM (zip as alphas) $ \(x, t) -> do
                      x1 <-
                        letSubExp (baseString x ++ "_elem_1") $
                          BasicOp $ Index x $ addFixIdx2FullSlice im1 t
                      x2 <-
                        letSubExp (baseString x ++ "_elem_2") $
                          BasicOp $ Index x $ addFixIdx2FullSlice nmi t
                      return (x1, x2)
                    return (unzip tmp)
                  addStms stms
                  resultBodyM (rs1 ++ rs2)
              )
              (resultBodyM (ne ++ ne))
          ]
    mkIdxStm idx (t, r_arr, r) =
      mkLet [Ident r t] $ BasicOp $ Index r_arr $ addFixIdx2FullSlice idx t
--
-- previous buggy version is unreachable now
-- diffReduce ops pat_adj w as red = do
--   red' <- renameRed red
--   flip_red <- renameRed =<< flipReduce red
--   ls <- scanExc "ls" (redToScan red') as
--   rs <-
--     mapM eReverse
--       =<< scanExc "ls" (redToScan flip_red)
--       =<< mapM eReverse as

--   (as_params, f) <- mkF $ redLambda red

--   f_adj <- vjpLambda ops (map adjFromVar pat_adj) as_params f

--   as_adj <- letTupExp "adjs" $ Op $ Screma w (ls ++ as ++ rs) (mapSOAC f_adj)

--   zipWithM_ updateAdj as as_adj
--   where
--     renameRed (Reduce comm lam nes) =
--       Reduce comm <$> renameLambda lam <*> pure nes

--     redToScan :: Reduce SOACS -> Scan SOACS
--     redToScan (Reduce _ lam nes) = Scan lam nes
--     flipReduce (Reduce comm lam nes) = do
--       lam' <- renameLambda lam {lambdaParams = flipParams $ lambdaParams lam}
--       pure $ Reduce comm lam' nes
--     flipParams ps = uncurry (flip (++)) $ splitAt (length ps `div` 2) ps

--
-- Special case of reduce with min/max:
--    let x = reduce minmax ne as
-- Forward trace (assuming w = length as):
--    let (x, x_ind) =
--      reduce (\ acc_v acc_i v i ->
--                 if (acc_v == v) then (acc_v, min acc_i i)
--                 else if (acc_v == minmax acc_v v)
--                      then (acc_v, acc_i)
--                      else (v, i))
--             (ne_min, -1)
--             (zip as (iota w))
-- Reverse trace:
--    num_elems = i64.bool (0 <= x_ind)
--    m_bar_repl = replicate num_elems m_bar
--    as_bar[x_ind:num_elems:1] += m_bar_repl
diffMinMaxReduce ::
  VjpOps -> VName -> StmAux () -> SubExp -> BinOp -> SubExp -> VName -> ADM () -> ADM ()
diffMinMaxReduce _ops x aux w minmax ne as m = do
  let t = binOpType minmax

  acc_v_p <- newParam "acc_v" $ Prim t
  acc_i_p <- newParam "acc_i" $ Prim int64
  v_p <- newParam "v" $ Prim t
  i_p <- newParam "i" $ Prim int64
  red_lam <-
    mkLambda [acc_v_p, acc_i_p, v_p, i_p] $
      fmap varsRes . letTupExp "idx_res"
        =<< eIf
          (eCmpOp (CmpEq t) (eParam acc_v_p) (eParam v_p))
          ( eBody
              [ eParam acc_v_p,
                eBinOp (SMin Int64) (eParam acc_i_p) (eParam i_p)
              ]
          )
          ( eBody
              [ eIf
                  ( eCmpOp
                      (CmpEq t)
                      (eParam acc_v_p)
                      (eBinOp minmax (eParam acc_v_p) (eParam v_p))
                  )
                  (eBody [eParam acc_v_p, eParam acc_i_p])
                  (eBody [eParam v_p, eParam i_p])
              ]
          )

  red_iota <-
    letExp "red_iota" $
      BasicOp $ Iota w (intConst Int64 0) (intConst Int64 1) Int64
  form <- reduceSOAC [Reduce Commutative red_lam [ne, intConst Int64 (-1)]]
  x_ind <- newVName (baseString x <> "_ind")
  auxing aux $ letBindNames [x, x_ind] $ Op $ Screma w [as, red_iota] form

  m

  x_adj <- lookupAdjVal x
  in_bounds <-
    letSubExp "minmax_in_bounds" . BasicOp $
      CmpOp (CmpSlt Int64) (intConst Int64 0) w
  updateAdjIndex as (CheckBounds (Just in_bounds), Var x_ind) (Var x_adj)

onePrim :: PrimType -> PrimValue
onePrim (IntType it) = IntValue $ intValue it (1 :: Int)
onePrim (FloatType ft) = FloatValue $ floatValue ft (1 :: Double)
onePrim Bool = BoolValue True
onePrim Unit = UnitValue

constructAddBinOp :: PrimType -> BinOp
constructAddBinOp (IntType it) = Add it OverflowUndef
constructAddBinOp (FloatType ft) = FAdd ft
constructAddBinOp t = error $ "constructAddBinOp: " ++ pretty t

constructMultBinOp :: PrimType -> BinOp
constructMultBinOp (IntType it) = Mul it OverflowUndef
constructMultBinOp (FloatType ft) = FMul ft
constructMultBinOp t = error $ "constructMultBinOp: " ++ pretty t

constructDivBinOp :: PrimType -> BinOp
constructDivBinOp (IntType it) = SDiv it Unsafe
constructDivBinOp (FloatType ft) = FDiv ft
constructDivBinOp t = error $ "constructDivBinOp: " ++ pretty t

-- CODE EXAMPLE:
-- let x = reduce (*) (ne) [a1, a2, ..., ai, ..., a_n-1]
-- FORWARD TRACE:
--   pnz = map (\a -> if a==0 then 1 else a) as
--         |> reduce (*) ne
--   nzero = map (\a -> if a==0 then 1 else 0) as
--           |> reduce (+) 0
--    x = if nzero == 0 then pnz else 0
-- REVERSE TRACE:
--    as_contribs = map(\a -> if nzero == 0 then x/a * x_contribs
--                            else if nzero==1 then if a==0 then pnz * x_contribs
--                                                          else 0
--                            else 0) as
diffMult :: VjpOps -> VName -> SubExp -> BinOp -> SubExp -> VName -> ADM () -> ADM ()
diffMult _ops x w red ne as m = do
    let t = binOpType red
    --let typeZero = blankPrimValue t
    --let typeOne  = onePrim t
    --let addOp  = constructAddBinOp t
    --let multOp = constructMultBinOp t
    --let divOp  = constructDivBinOp t
    
    a <- newParam "a" $ Prim t
    
    pnz_map_lambda <-
      mkLambda [a] $ do
        vnm <- letExp "a_map"
          =<< eIf
            (eCmpOp (CmpEq t) (eParam a) (eSubExp (intConst Int64 0)))
            (eBody [(eSubExp ne)])
            (eBody [(eParam a)])
        
        return $ [varRes vnm]

    -- map (\a -> if a==0 then 1 else a) as
    pnz_map <- letExp "pnz_map" $
      Op $ Screma w [as] (mapSOAC pnz_map_lambda)

    acc_a <- newParam "acc_a" $ Prim t
    a_i <- newParam "a_i" $ Prim t
    pnz_red_lambda <-
      mkLambda [acc_a, a_i] $ do
        vnm <- letExp "a_red"
          =<<
            eBinOp
            (Mul Int64 OverflowUndef)
            (eParam acc_a) (eParam a_i)
        return $ [varRes vnm]
    
    pnz_red_form <-
      reduceSOAC [Reduce Commutative pnz_red_lambda [ne]]

    pnz <- letExp "pnz" $ Op $ Screma w [pnz_map] pnz_red_form

    b <- newParam "b" $ Prim t
    nzero_map_lambda <-
      mkLambda [b] $ do
        vnm <- letExp "b_map"
          =<< eIf
            (
              eCmpOp
                (CmpEq t) (eParam b) (eSubExp (intConst Int64 0))
            )
            (eBody [eSubExp (intConst Int64 1)])
            (eBody [eSubExp (intConst Int64 0)])
        return $ [varRes vnm]

    nzero_map <- letExp "nzero_map" $ Op $ Screma w [as] (mapSOAC nzero_map_lambda)

    acc_b <- newParam "acc_b" $ Prim t
    b_i <- newParam "b_i" $ Prim t
    nzero_red_lambda <-
      mkLambda [acc_b, b_i] $ do
        vnm <- letExp "b_red"
          =<< eBinOp (Add Int64 OverflowUndef) (eParam acc_b) (eParam b_i)
        return $ [varRes vnm]
    
    nzero_red_form <-
      reduceSOAC [Reduce Commutative nzero_red_lambda [intConst Int64 0]]
      
    nzero <- letExp "nzero" $ Op $ Screma w [nzero_map] nzero_red_form

    has_zero_exp <-
      eIf
      (
        eCmpOp (CmpEq t) (eSubExp (Var nzero)) (eSubExp (intConst Int64 0))
      )
      (eBody [eSubExp (Var pnz)])
      (eBody [eSubExp (intConst Int64 0)])

    letBindNames [x] has_zero_exp
    
    m

    c <- newParam "c" $ Prim t
    x_adj <- lookupAdjVal x
    as_contribs_lambda <-
      mkLambda [c] $ do
        vnm <- letExp "c_res"
          =<< eIf  -- if nzero == 0
            (
              eCmpOp
                (CmpEq t) (eSubExp (Var nzero)) (eSubExp (intConst Int64 0))
            )
            (eBody  -- x/a * x_contribs
              [
                eBinOp (Mul Int64 OverflowUndef)
                  (eBinOp (SDiv Int64 Unsafe) (eSubExp (Var x)) (eParam c))
                  (eSubExp (Var x_adj))
              ]
            )
            (eBody
              [
                eIf -- else if nzero == 1
                  (eCmpOp
                      (CmpEq t) (eSubExp (Var nzero)) (eSubExp (intConst Int64 1)))
                  (
                    eBody
                      [
                        eIf -- if a == 0
                          (
                          eCmpOp
                            (CmpEq t) (eParam c) (eSubExp (intConst Int64 0))
                          )
                          (eBody [ -- pnz * x_contribs
                            eBinOp (Mul Int64 OverflowUndef)
                            (eSubExp (Var pnz)) (eSubExp (Var x_adj))
                            ])
                          (eBody [eSubExp (intConst Int64 0)])
                      ]
                  )
                  (eBody [eSubExp (intConst Int64 0)])
              ]
            )
        return [varRes vnm]

    x_contribs <- letExp "x_contribs" $ Op $ Screma w [as] (mapSOAC as_contribs_lambda)

    updateAdj as x_contribs