{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Futhark.AD.Rev.Reduce_by_index
  ( diffHist)
where

import Control.Monad
import Futhark.AD.Rev.Monad
import Futhark.AD.Rev.Map
import Futhark.Analysis.PrimExp.Convert
import Futhark.Builder
import Futhark.IR.SOACS
import Futhark.Tools
import Futhark.Transform.Rename

data FirstOrSecond = WrtFirst | WrtSecond

-- computes `d(x op y)/dx` or d(x op y)/dy
mkScanAdjointLam :: VjpOps -> Lambda SOACS -> FirstOrSecond -> ADM (Lambda SOACS)
mkScanAdjointLam ops lam0 which = do
  let len = length $ lambdaReturnType lam0
  lam <- renameLambda lam0
  let p2diff =
        case which of
          WrtFirst -> take len $ lambdaParams lam
          WrtSecond -> drop len $ lambdaParams lam
  p_adjs <- mapM unitAdjOfType (lambdaReturnType lam)
  vjpLambda ops p_adjs (map paramName p2diff) lam


onePrimValue :: PrimType -> PrimValue
onePrimValue (IntType Int8) = IntValue $ Int8Value 1
onePrimValue (IntType Int16) = IntValue $ Int16Value 1
onePrimValue (IntType Int32) = IntValue $ Int32Value 1
onePrimValue (IntType Int64) = IntValue $ Int64Value 1
onePrimValue (FloatType Float32) = FloatValue $ Float32Value 1.0
onePrimValue (FloatType Float64) = FloatValue $ Float64Value 1.0
onePrimValue Bool = BoolValue True
onePrimValue _ = error "In onePrimValue, Reduce_by_index.hs: input not supported"

getBinOpPlus :: PrimType -> BinOp
getBinOpPlus (IntType x) = Add x OverflowUndef
getBinOpPlus (FloatType f) = FAdd f
getBinOpPlus _ = error "In getBinOpMul, Reduce_by_index.hs: input not supported"


withinBounds :: [(SubExp, VName)] -> TPrimExp Bool VName
withinBounds [] = TPrimExp $ ValueExp (BoolValue True)
withinBounds [(q, i)] = (le64 i .<. pe64 q) .&&. (pe64 (intConst Int64 (-1)) .<. le64 i)
withinBounds (qi : qis) = withinBounds [qi] .&&. withinBounds qis

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

genIdxLamBdy :: VName -> [(SubExp, Param Type)] -> Type -> ADM (Body SOACS)
genIdxLamBdy as wpis = genRecLamBdy as wpis []
  where
    genRecLamBdy :: VName -> [(SubExp, Param Type)] -> [Param Type] -> Type -> ADM (Body SOACS)
    genRecLamBdy arr w_pis nest_pis (Array t (Shape []) _) =
      genRecLamBdy arr w_pis nest_pis (Prim t)
    genRecLamBdy arr w_pis nest_pis (Array t (Shape (s : ss)) _) = do
      new_ip <- newParam "i" (Prim int64)
      let t' = Prim t `arrayOfShape` Shape ss
      inner_lam <-
        mkLambda [new_ip] $
          bodyBind =<< genRecLamBdy arr w_pis (nest_pis ++ [new_ip]) t'
      let (_, orig_pis) = unzip w_pis
      buildBody_ . localScope (scopeOfLParams (orig_pis ++ nest_pis)) $ do
        iota_v <- letExp "iota" $ BasicOp $ Iota s (intConst Int64 0) (intConst Int64 1) Int64
        r <- letSubExp (baseString arr ++ "_elem") $ Op $ Screma s [iota_v] (mapSOAC inner_lam)
        pure [subExpRes r]
    genRecLamBdy arr w_pis nest_pis (Prim ptp) = do
      let (ws, orig_pis) = unzip w_pis
      let inds = map paramName (orig_pis ++ nest_pis)
      localScope (scopeOfLParams (orig_pis ++ nest_pis)) $
        eBody
          [ eIf
              (toExp $ withinBounds $ zip ws $ map paramName orig_pis)
              ( do
                  r <- letSubExp "res" $ BasicOp $ Index arr $ Slice $ map (DimFix . Var) inds
                  resultBodyM [r]
              )
              (resultBodyM [Constant $ blankPrimValue ptp])
          ]
    genRecLamBdy _ _ _ _ = error "In Reduce_by_index.hs, helper function genRecLamBdy, unreachable case reached!"

-- Pattern Matches special lambda cases:
--   plus, multiplication, min, max, which are all commutative.
-- Succeeds for (\ x y -> x binop y) or (\x y -> y binop x).
isSpecOpLam :: (BinOp -> Maybe BinOp) -> Lambda SOACS -> Maybe BinOp
isSpecOpLam isOp lam =
  isRedStm
    (map paramName $ lambdaParams lam)
    (map resSubExp $ bodyResult $ lambdaBody lam)
    (stmsToList $ bodyStms $ lambdaBody lam)
  where
    isRedStm [a, b] [r] [Let (Pat [pe]) _aux (BasicOp (BinOp op x y))] =
      if (r == Var (patElemName pe)) && ((x == Var a && y == Var b) || (x == Var b && y == Var a))
        then isOp op
        else Nothing
    isRedStm _ _ _ = Nothing

isAddTowLam :: Lambda SOACS -> Maybe BinOp
isAddTowLam lam = isSpecOpLam isAddOp $ filterMapOp lam
  where
    isAddOp bop@(Add _ _) = Just bop
    isAddOp bop@(FAdd _) = Just bop
    isAddOp _ = Nothing
    filterMapOp (Lambda [pa1, pa2] lam_body _)
      | [r] <- bodyResult lam_body,
        [map_stm] <- stmsToList (bodyStms lam_body),
        (Let pat _ (Op scrm)) <- map_stm,
        (Pat [pe]) <- pat,
        (Screma _ [a1, a2] (ScremaForm [] [] map_lam)) <- scrm,
        (a1 == paramName pa1 && a2 == paramName pa2) || (a1 == paramName pa2 && a2 == paramName pa1),
        r == subExpRes (Var (patElemName pe)) =
        filterMapOp map_lam
    filterMapOp other_lam = other_lam

isMulLam :: Lambda SOACS -> Maybe BinOp
isMulLam = isSpecOpLam isMulOp
  where
    isMulOp bop@(Mul _ _) = Just bop
    isMulOp bop@(FMul _) = Just bop
    isMulOp _ = Nothing

isMinMaxLam :: Lambda SOACS -> Maybe BinOp
isMinMaxLam = isSpecOpLam isMinMaxOp
  where
    isMinMaxOp bop@(SMin _) = Just bop
    isMinMaxOp bop@(UMin _) = Just bop
    isMinMaxOp bop@(FMin _) = Just bop
    isMinMaxOp bop@(SMax _) = Just bop
    isMinMaxOp bop@(UMax _) = Just bop
    isMinMaxOp bop@(FMax _) = Just bop
    isMinMaxOp _ = Nothing

mind_eq_min1 :: VName -> PrimExp VName
mind_eq_min1 ind =
  CmpOpExp
    (CmpEq (IntType Int64))
    (LeafExp ind int64)
    (ValueExp (IntValue $ Int64Value (-1)))

-- generates the lambda for the extended operator of min/max:
-- meaning the min/max value tupled with the minimal index where
--   that value was found (when duplicates exist). We use `-1` as
--   the neutral element of the index.
mkMinMaxIndLam :: PrimType -> BinOp -> ADM (Lambda SOACS)
mkMinMaxIndLam ptp minmax_op = do
  fargs_vals <- mapM (`newParam` Prim ptp) ["acc_v", "arg_v"]
  fargs_inds <- mapM (`newParam` Prim int64) ["acc_ind", "arg_ind"]
  let ([facc_v, farg_v], [facc_i, farg_i]) = (fargs_vals, fargs_inds)
  let [acc_v, arg_v, acc_i, arg_i] = map paramName (fargs_vals ++ fargs_inds)
  let (cmp1, cmp2) = get_cmp_pexp minmax_op acc_v arg_v
  red_lam_bdy <-
    runBodyBuilder . localScope (scopeOfLParams (fargs_vals ++ fargs_inds)) $
      eBody
        [ eIf
            (toExp cmp1)
            ( do
                res_ind <- letSubExp "minmax" =<< toExp (min_idx_pexp acc_i arg_i)
                resultBodyM [Var acc_v, res_ind]
            )
            ( eBody
                [ eIf
                    (toExp cmp2)
                    (resultBodyM [Var acc_v, Var acc_i])
                    (resultBodyM [Var arg_v, Var arg_i])
                ]
            )
        ]
  return $ Lambda [facc_v, facc_i, farg_v, farg_i] red_lam_bdy [Prim ptp, Prim int64]
  where
    min_idx_pexp i1 i2 = BinOpExp (SMin Int64) (LeafExp i1 int64) (LeafExp i2 int64)
    get_cmp_pexp bop facc farg =
      let [leaf_acc, leaf_arg] = map (`LeafExp` ptp) [facc, farg]
       in ( CmpOpExp (CmpEq ptp) leaf_acc leaf_arg,
            CmpOpExp (CmpEq ptp) leaf_acc $ BinOpExp bop leaf_acc leaf_arg
          )

peElemEq0 :: PrimType -> Param Type -> PrimExp VName
peElemEq0 ptp farg =
  CmpOpExp
    (CmpEq ptp)
    (LeafExp (paramName farg) ptp)
    (ValueExp (blankPrimValue ptp))

helperMulOp1 :: PrimType -> BinOp -> ADM (Lambda SOACS, Lambda SOACS)
helperMulOp1 ptp bop = do
  -- on forward sweep: create the map lambda
  let eltp = Prim ptp
  farg <- newParam "arg" eltp
  map_lam_bdy <-
    runBodyBuilder . localScope (scopeOfLParams [farg]) $
      eBody
        [ eIf
            (toExp $ peElemEq0 ptp farg)
            (resultBodyM [Constant $ onePrimValue ptp, intConst Int64 1])
            (resultBodyM [Var (paramName farg), intConst Int64 0])
        ]
  let map_lam = Lambda [farg] map_lam_bdy [eltp, Prim int64]
  -- still on forward sweep: create the reduce lambda [*, +]
  fargs_prod <- mapM (`newParam` eltp) ["acc_prod", "arg_val"]
  fargs_count <- mapM (`newParam` Prim int64) ["acc_count", "arg_count"]
  let ([acc_v, arg_v], [acc_c, arg_c]) = (fargs_prod, fargs_count)
  red_lam_bdy <- runBodyBuilder . localScope (scopeOfLParams (fargs_prod ++ fargs_count)) $ do
    r_prod <-
      letSubExp "res_prod" $
        BasicOp $
          BinOp
            bop
            (Var $ paramName acc_v)
            (Var $ paramName arg_v)
    r_count <- letSubExp "res_count" =<< toExp (le64 (paramName acc_c) + le64 (paramName arg_c))
    resultBodyM [r_prod, r_count]
  let red_lam = Lambda [acc_v, acc_c, arg_v, arg_c] red_lam_bdy [eltp, Prim int64]
  return (map_lam, red_lam)

helperMulOp2 :: PrimType -> VName -> VName -> VName -> ADM (Stms SOACS)
helperMulOp2 ptp nz_prod zr_count prod = do
  -- on forward sweep: if statement to recover the potentially-zero product
  let ps = [Param mempty nz_prod $ Prim ptp, Param mempty zr_count $ Prim int64]
  runBuilder_ . localScope (scopeOfLParams ps) $ do
    tmps <-
      letTupExp "tmp_if_res"
        =<< eIf
          (toExp $ le64 zr_count .>. pe64 (intConst Int64 0))
          (resultBodyM [Constant $ blankPrimValue ptp])
          (resultBodyM [Var nz_prod])
    addStm (mkLet [Ident prod $ Prim ptp] $ BasicOp $ SubExp $ Var $ head tmps)

helperMulOp3 :: PrimType -> BinOp -> VName -> VName -> Param Type -> VName -> ADM (Body SOACS)
helperMulOp3 ptp bop nz_prod zr_count fa_orig prod_bar = do
  -- if zero_count == 0 then (nz_prod / a) * p_bar
  --                            else if zero_count == 1 && a == 0
  --                                 then nz_prod * p_bar
  --                                 else 0
  let params = [Param mempty nz_prod $ Prim ptp,
                Param mempty zr_count $ Prim int64,
                Param mempty prod_bar $ Prim ptp]
  runBodyBuilder . localScope (scopeOfLParams (fa_orig : params)) $
    eBody
      [ eIf
          (toExp $ le64 zr_count .<. pe64 (intConst Int64 1))
          ( do
              div_se <-
                letSubExp "div_res" $
                  BasicOp $
                    BinOp
                      (getBinOpDiv bop)
                      (Var nz_prod)
                      (Var $ paramName fa_orig)
              res_se <- letSubExp "res_ctrb" $ BasicOp $ BinOp bop div_se (Var prod_bar)
              resultBodyM [res_se]
          )
          ( eBody
              [ eIf
                  (toExp $ BinOpExp LogAnd (peElemEq0 ptp fa_orig) (eqToOne zr_count))
                  ( do
                      res_se <-
                        letSubExp "res_ctrb" $
                          BasicOp $
                            BinOp
                              bop
                              (Var nz_prod)
                              (Var prod_bar)
                      resultBodyM [res_se]
                  )
                  (resultBodyM [Constant $ blankPrimValue ptp])
              ]
          )
      ]
  where
    eqToOne v_nm = CmpOpExp (CmpEq int64) (LeafExp v_nm int64) (ValueExp $ IntValue $ Int64Value 1)
    getBinOpDiv (Mul t _) = SDiv t Unsafe
    getBinOpDiv (FMul t) = FDiv t
    getBinOpDiv _ = error "In Reduce_by_index.hs, getBinOpDiv, unreachable case reached!"

-- tmp = map (\(i,f) -> if f then (ne, f) else (vals[i-1], f)) (iota n) (flags)
-- scan (\(v1,f1) (v2,f2) ->
--            let f = f1 || f2
--            let v = if f2 then v2 else op v1 v2
--            in (v, f)) tmp flags

-- Lift a lambda to produce an exlusive segmented scan operator.
mkSegScanExc :: Lambda SOACS -> [SubExp] -> SubExp -> VName -> VName -> ADM (SOAC SOACS) 
mkSegScanExc lam ne n vals flags = do
  -- Get lambda return type
  let rt = lambdaReturnType lam
  -- v <- mapM (newParam "v") rt
  v1 <- mapM (newParam "v1") rt
  v2 <- mapM (newParam "v2") rt
  f <- newParam "f" $ Prim int8
  f1 <- newParam "f1" $ Prim int8
  f2 <- newParam "f2" $ Prim int8
  let params = (f1 : v1) ++ (f2 : v2)

  iota_n <- letExp "iota_n" $ BasicOp $ Iota n (intConst Int64 0) (intConst Int64 1) Int64
  i <- newParam "i" $ Prim int64

  -- (\(flag, i) -> if f then (f, ne) else (f, vals[i-1]))

  tmp_lam_body <- runBodyBuilder . localScope (scopeOfLParams [f, i]) $ do
    idx_minus_one <- letSubExp "idx_minus_one" $ BasicOp $ BinOp (Sub Int64 OverflowUndef) (Var $ paramName i) (intConst Int64 1)
    prev_elem <- letTupExp "prev_elem" $ BasicOp $ Index vals (fullSlice (Prim int64) [DimFix idx_minus_one])
    
    let f_check =
          eCmpOp
            (CmpEq $ IntType Int8)
            (eSubExp $ Var $ paramName f)
            (eSubExp $ intConst Int8 1)

    eBody
      [
        eIf
          f_check
          (resultBodyM $ (Var $ paramName f) : ne )
          (resultBodyM $ ((Var . paramName) f) : (map Var prev_elem))
      ]

  let tmp_lam = Lambda [f, i] tmp_lam_body (Prim int8 : rt)
  lam' <- renameLambda lam
  
  scan_body <- runBodyBuilder . localScope (scopeOfLParams params) $ do
    -- f = f1 || f2
    f' <- letSubExp "f'" $ BasicOp $ BinOp (Or Int8 ) (Var $ paramName f1) (Var $ paramName f2)
    -- v = if f2 then v2 else (lam v1 v2)     
    op_body <- mkLambda (v1++v2) $ do
      eLambda lam' (map (eSubExp . Var . paramName) (v1++v2))

    v2_body <- eBody $ map (eSubExp . Var . paramName) v2

    f_check <- letExp "f_check" $ BasicOp $ CmpOp (CmpEq $ IntType Int8) (Var $ paramName f2) (intConst Int8 1)

    v <- letSubExp "v" $
          If (Var f_check)
          v2_body
          (lambdaBody op_body)
          (IfDec (staticShapes rt) IfNormal)
    
    -- Put together
    eBody $ map eSubExp ([f', v])
  
  let scan_lambda = Lambda params scan_body (Prim int8 : rt)

  return $ Screma n [flags, iota_n] $ ScremaForm [Scan scan_lambda ((intConst Int8 0) : ne)] [] tmp_lam

mkF :: Lambda SOACS -> ADM ([VName], Lambda SOACS)
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

-- partion2Maker - Takes flag array and values and creates a scatter SOAC
--                  which corresponds to the partition2 of the inputs
-- partition2Maker size flags values = 
partition2Maker :: SubExp -> VName -> VName -> BuilderT SOACS ADM (SOAC SOACS)
partition2Maker n flags xs = do
  
  let bitType = int64
  let zeroSubExp = Constant $ IntValue $ intValue Int64 (0 :: Integer)
  let oneSubExp = Constant $ IntValue $ intValue Int64 (1 :: Integer)

  -- let bits_inv = map (\b -> 1 - b) bits
  flag <- newParam "flag" $ Prim bitType
  bits_inv_map_bdy <- runBodyBuilder . localScope (scopeOfLParams [flag]) $ do
    eBody
      [
        eBinOp (Sub Int64 OverflowUndef)
        (eSubExp $ oneSubExp)
        (eParam flag)
      ]
  let bits_inv_map_lam = Lambda [flag] bits_inv_map_bdy [Prim bitType]
  flags_inv <- letExp "flags_inv" $ Op $ Screma n [flags] (ScremaForm [] [] bits_inv_map_lam)

  -- let ps0 = scan (+) 0 (flags_inv)
  ps0_add_lam <- binOpLambda (Add Int64 OverflowUndef) bitType
  let ps0_add_scan = Scan ps0_add_lam [zeroSubExp]
  f' <- mkIdentityLambda [Prim bitType]
  ps0 <- letExp "ps0" $ Op $ Screma n [flags_inv] (ScremaForm [ps0_add_scan] [] f')

  -- let ps0_clean = map2 (*) flags_inv ps0 
  ps0clean_mul_lam <- binOpLambda (Mul Int64 OverflowUndef) bitType
  ps0clean <- letExp "ps0_clean" $ Op $ Screma n [flags_inv, ps0] (ScremaForm [] [] ps0clean_mul_lam)

  -- let ps0_offset = reduce (+) 0 flags_inv    
  ps0off_add_lam <- binOpLambda (Add Int64 OverflowUndef) bitType
  ps0off_red <- reduceSOAC [Reduce Commutative ps0off_add_lam [intConst Int64 0]]
  ps0off <- letExp "ps0_offset" $ Op $ Screma n [flags_inv] ps0off_red

  -- let ps1 = scan (+) 0 flags
  ps1_scanlam <- binOpLambda (Add Int64 OverflowUndef) bitType
  let ps1_scan = Scan ps1_scanlam [zeroSubExp]
  f'' <- mkIdentityLambda [Prim bitType]
  ps1 <- letExp "ps1" $ Op $ Screma n [flags] (ScremaForm [ps1_scan] [] f'')

  -- let ps1' = map (+ps0_offset) ps1
  ps1_val <- newParam "ps1_val" $ Prim bitType
  ps1clean_lam_bdy <- runBodyBuilder . localScope (scopeOfLParams [ps1_val]) $ do
    eBody
      [
        eBinOp (Add Int64 OverflowUndef)
        (eParam ps1_val)
        (eSubExp $ Var ps0off)
      ]
  let ps1clean_lam = Lambda [ps1_val] ps1clean_lam_bdy [Prim bitType]
  ps1' <- letExp "ps1'" $ Op $ Screma n [ps1] (ScremaForm [] [] ps1clean_lam)

  -- let ps1_clean = map2 (*) flags ps1'
  ps1cleanprim_mul_lam <- binOpLambda (Mul Int64 OverflowUndef) bitType
  ps1_clean <- letExp "ps1_clean" $ Op $ Screma n [flags, ps1'] (ScremaForm [] [] ps1cleanprim_mul_lam)

  -- let ps = map2 (+) ps0_clean ps1_clean
  ps_add_lam <- binOpLambda (Add Int64 OverflowUndef) bitType
  ps <- letExp "ps" $ Op $ Screma n [ps0clean, ps1_clean] (ScremaForm [] [] ps_add_lam)


  -- let ps_actual = map (-1) ps
  psactual_x <- newParam "psactual_x" $ Prim bitType
  psactual_lam_bdy <- runBodyBuilder . localScope (scopeOfLParams [psactual_x]) $ do
    eBody
      [
        eBinOp (Sub Int64 OverflowUndef)
        (eParam psactual_x)
        (eSubExp $ oneSubExp)
      ]
  let psactual_lam = Lambda [psactual_x] psactual_lam_bdy [Prim bitType]
  psactual <- letExp "psactual" $ Op $ Screma n [ps] (ScremaForm [] [] psactual_lam)
  
  -- let scatter_inds = scatter inds ps_actual inds
  -- return scatter_inds
  f''' <- mkIdentityLambda [Prim int64, Prim int64]
  xs_cpy <- letExp (baseString xs ++ "_copy") $ BasicOp $ Copy xs
  return $ Scatter n [psactual, xs] f''' [(Shape [n], 1, xs_cpy)]


getMulOp :: Type -> BinOp
getMulOp (Prim t) = case t of
                      (IntType t')   -> Mul t' OverflowUndef
                      (FloatType t') -> FMul t'
                      _              -> error $ "Unsupported type in getMulOp"
getMulOp _        = error $ "Unsupported type in getMulOp"

getBaseAdj :: Type -> SubExp
getBaseAdj (Prim (IntType Int8))  = Constant $ IntValue $ Int8Value 0
getBaseAdj (Prim (IntType Int16)) = Constant $ IntValue $ Int16Value 0
getBaseAdj (Prim (IntType Int32)) = Constant $ IntValue $ Int32Value 0
getBaseAdj (Prim (IntType Int64)) = Constant $ IntValue $ Int64Value 0
getBaseAdj (Prim (FloatType Float32)) = Constant $ FloatValue $ Float32Value 0.0
getBaseAdj (Prim (FloatType Float64)) = Constant $ FloatValue $ Float64Value 0.0
getBaseAdj _ = error "In getBaseAdj, Reduce_by_index.hs: input not supported"

-- Takes name of two params, a binOp and the type of params and gives a lambda of that application
mkSimpleLambda :: String -> String -> BinOp -> Type -> ADM (Lambda SOACS)
mkSimpleLambda x_name y_name binOp t = do
  x <- newParam x_name t
  y <- newParam y_name t
  lam_body <- runBodyBuilder . localScope (scopeOfLParams [x,y]) $ do
    eBody
      [
        eBinOp binOp
        (eParam x)
        (eParam y)
      ]
  return $ Lambda [x, y] lam_body [t]

diffHist :: VjpOps -> Pat Type -> StmAux() -> SOAC SOACS -> ADM () -> ADM ()
-- Special case (+)
diffHist _vjops pat aux soac m
  | (Hist n [inds, vs] hist_add bucket_fun) <- soac,
    [HistOp shape rf [orig_dst] [ne] add_lam] <- hist_add,
    Just _ <- isAddTowLam add_lam,
    [pe] <- patNames pat = do
    -- need to create a copy of the orig histo, because the reverse trace might need
    -- the values of the original histogram input!
    dst_cpy <- letExp (baseString orig_dst ++ "_copy") $ BasicOp $ Copy orig_dst
    let histo' = Hist n [inds, vs] [HistOp shape rf [dst_cpy] [ne] add_lam] bucket_fun
    addStm $ Let pat aux $ Op histo'
    m
    -- Reverse trace
    let eltp = head $ lambdaReturnType add_lam
    pe_bar <- lookupAdjVal $ pe
    -- already update orig_dst bar
    void $ updateAdj orig_dst pe_bar
    -- update the vs bar; create a map nest with the branch innermost so all
    -- parallelism can be exploited.
    pind <- newParam "index" $ Prim int64
    map_bar_lam_bdy <- genIdxLamBdy pe_bar [(n, pind)] eltp
    let map_bar_lam = Lambda [pind] map_bar_lam_bdy [eltp]
    vs_bar <- letExp (baseString vs ++ "_bar") $ Op $ Screma n [inds] (mapSOAC map_bar_lam)
    void $ updateAdj vs vs_bar

-- Special case min/max
diffHist _vjops (Pat [pe]) aux soac m
  | (Hist n [inds, vs] hist_max bucket_fun) <- soac,
    True <- isIdentityLambda bucket_fun,
    [HistOp shape rf [orig_dst] [ne] max_lam] <- hist_max,
    Just bop <- isMinMaxLam max_lam,
    [eltp] <- lambdaReturnType max_lam,
    p <- patElemName pe,
    Prim ptp <- eltp,
    [shapedim] <- shapeDims shape = do
  
    -- forward sweep makes a copy of the consumed array and computes a lifted histo
    orig_dst_cpy <- letExp (baseString orig_dst ++ "_cpy") $ BasicOp $ Copy orig_dst
    f' <- mkIdentityLambda [Prim int64, eltp, Prim int64]
    repl <- letExp "minus_ones" $ BasicOp $ Replicate shape (intConst Int64 (-1))
    maxind_lam <- mkMinMaxIndLam ptp bop
    
    let hist_op = HistOp shape rf [orig_dst_cpy, repl] [ne, intConst Int64 (-1)] maxind_lam
    iota_n <- letExp "iota_n" $ BasicOp $ Iota n (intConst Int64 0) (intConst Int64 1) Int64
    hist_inds <- newVName "hist_inds"
    let histo_pat = Pat [pe, PatElem hist_inds (mkI64ArrType shape)]
    auxing aux $ letBind histo_pat $ Op $ Hist n [inds, vs, iota_n] [hist_op] f'
    m
    -- reverse sweep:
    pe_bar <- lookupAdjVal p
    -- create the bar of `orig_dst` by means of a map:
    pis_h <- zipWithM newParam ["min_ind", "h_elem"] [Prim int64, eltp]
    let [min_ind_h, h_elem_h] = map paramName pis_h
    lam_bdy_hist_bar <-
      runBodyBuilder . localScope (scopeOfLParams pis_h) $
        eBody
          [ eIf
              (toExp $ mind_eq_min1 min_ind_h)
              (resultBodyM [Var h_elem_h])
              (resultBodyM [Constant $ blankPrimValue ptp])
          ]
    let lam_hist_bar = Lambda pis_h lam_bdy_hist_bar [eltp]
    hist_bar <-
      letExp (baseString orig_dst ++ "_bar") $
        Op $
          Screma shapedim [hist_inds, pe_bar] (ScremaForm [] [] lam_hist_bar)
    insAdj orig_dst hist_bar
    -- update vs_bar with a map and a scatter
    vs_bar <- lookupAdjVal vs
    pis_v <- zipWithM newParam ["min_ind", "h_elem"] [Prim int64, eltp]
    let [min_ind_v, h_elem_v] = map paramName pis_v
    lam_bdy_vs_bar <-
      runBodyBuilder . localScope (scopeOfLParams pis_v) $
        eBody
          [ eIf
              (toExp $ mind_eq_min1 min_ind_v)
              (resultBodyM [Constant $ blankPrimValue ptp])
              ( do
                  vs_bar_i <-
                    letSubExp (baseString vs_bar ++ "_el") $
                      BasicOp $
                        Index vs_bar $ Slice $ [DimFix $ Var min_ind_v]
                  let plus_op = getBinOpPlus ptp
                  r <- letSubExp "r" $ BasicOp $ BinOp plus_op vs_bar_i $ Var h_elem_v
                  resultBodyM [r]
              )
          ]
    let lam_vs_bar = Lambda pis_v lam_bdy_vs_bar [eltp]
    vs_bar_p <-
      letExp (baseString vs_bar ++ "_partial") $
        Op $
          Screma shapedim [hist_inds, pe_bar] (ScremaForm [] [] lam_vs_bar)
    f'' <- mkIdentityLambda [Prim int64, eltp]
    let scatter_soac = Scatter shapedim [hist_inds, vs_bar_p] f'' [(Shape [n], 1, vs_bar)]
    vs_bar' <- letExp (baseString vs ++ "_bar") $ Op scatter_soac
    insAdj vs vs_bar'
  where
    mkI64ArrType shape = arrayOf (Prim int64) shape NoUniqueness
--special case *
-- diffHist _vjops (Pat [pe]) aux soac m 
--   | (Hist n [inds, vs] hist_mul bucket_fun) <- soac,
--     True <- isIdentityLambda bucket_fun,
--     [HistOp shape rf [orig_dst] [ne] mul_lam] <- hist_mul,
--     Just mulop <- isMulLam mul_lam,
--     [eltp] <- lambdaReturnType mul_lam,
--     Prim ptp <- eltp,
--     [shapedim] <- shapeDims shape = do
--     -- starts here:
--     let pe_tp = patElemDec pe
--     (map_lam, _) <- helperMulOp1 ptp mulop
--     vs_lift <- letTupExp "nzel_zrct" $ Op $ Screma n [vs] (ScremaForm [] [] map_lam)
--     let [nz_vs, one_zrs] = vs_lift
--     zr_counts0 <- letExp "zr_cts" $ BasicOp $ Replicate shape (intConst Int64 0)
--     nz_prods0 <- letExp "nz_prd" $ BasicOp $ Replicate shape ne
--     nz_prods <- newVName "non_zero_prod"
--     zr_counts <- newVName "zero_count"
--     lam_add <- mkLamAddI64
--     let hist_zrn = HistOp shape rf [zr_counts0] [intConst Int64 0] lam_add
--     let hist_nzp = HistOp shape rf [nz_prods0] [ne] mul_lam
--     f' <- mkIdentityLambda [Prim int64, Prim int64, eltp, Prim int64]
--     let soac_pat =
--           Pat
--             [ PatElem nz_prods pe_tp,
--               PatElem zr_counts $
--               arrayOf (Prim int64) shape NoUniqueness
--             ]
--     let soac_exp = Op $ Hist n [inds, inds, nz_vs, one_zrs] [hist_nzp, hist_zrn] f'
--     auxing aux $ letBind soac_pat soac_exp
--     -- construct the histo result:
--     res_part <- newVName "res_part"
--     ps2 <- zipWithM newParam ["nz_pr", "zr_ct"] [eltp, Prim int64]
--     let [nz_prod, zr_count] = map paramName ps2
--     if_stms <- helperMulOp2 ptp nz_prod zr_count res_part
--     lam_bdy_2 <- runBodyBuilder . localScope (scopeOfLParams ps2) $ do
--       addStms if_stms
--       resultBodyM [Var res_part]
--     h_part <-
--       letExp "hist_part" $
--         Op $
--           Screma
--             shapedim
--             [nz_prods, zr_counts]
--             (ScremaForm [] [] (Lambda ps2 lam_bdy_2 [eltp]))
--     ps3 <- zipWithM newParam ["h_orig", "h_part"] [eltp, eltp]
--     let [ph_orig, ph_part] = map paramName ps3
--     lam_pe_bdy <- runBodyBuilder . localScope (scopeOfLParams ps3) $ do
--       r <- letSubExp "res" $ BasicOp $ BinOp mulop (Var ph_orig) (Var ph_part)
--       resultBodyM [r]
--     auxing aux $
--       letBind (Pat [pe]) $
--         Op $
--           Screma
--             shapedim
--             [orig_dst, h_part]
--             (ScremaForm [] [] (Lambda ps3 lam_pe_bdy [eltp]))
--     m
--     -- reverse trace
--     pe_bar <- lookupAdjVal $ patElemName pe
--     -- updates the orig_dst with its proper bar
--     mul_lam' <- renameLambda mul_lam
--     orig_bar <-
--       letTupExp (baseString orig_dst ++ "_bar") $
--         Op $
--           Screma
--             shapedim
--             [h_part, pe_bar]
--             (ScremaForm [] [] mul_lam')
--     zipWithM_ updateAdj [orig_dst] orig_bar
--     -- updates the partial histo result with its proper bar
--     mul_lam'' <- renameLambda mul_lam
--     part_bars <-
--       letTupExp (baseString h_part ++ "_bar") $
--         Op $
--           Screma
--             shapedim
--             [orig_dst, pe_bar]
--             (ScremaForm [] [] mul_lam'')
--     let [part_bar] = part_bars
--     -- add the contributions to each array element
--     pj <- newParam "j" (Prim int64)
--     pv <- newParam "v" eltp
--     let j = paramName pj
--     ((zr_cts, pr_bar, nz_prd), tmp_stms) <- runBuilderT' . localScope (scopeOfLParams [pj, pv]) $ do
--       zr_cts <- letExp "zr_cts" $ BasicOp $ Index zr_counts $ fullSlice eltp [DimFix (Var j)]
--       pr_bar <- letExp "pr_bar" $ BasicOp $ Index part_bar $ fullSlice eltp [DimFix (Var j)]
--       nz_prd <- letExp "nz_prd" $ BasicOp $ Index nz_prods $ Slice [DimFix (Var j)]
--       return (zr_cts, pr_bar, nz_prd)
--     bdy_tmp <- helperMulOp3 ptp mulop nz_prd zr_cts pv pr_bar
--     lam_bar <-
--       runBodyBuilder . localScope (scopeOfLParams [pj, pv]) $
--         eBody
--           [ eIf
--               (toExp $ withinBounds [(shapedim, j)])
--               ( do
--                   addStms (tmp_stms <> bodyStms bdy_tmp)
--                   resultBodyM (map resSubExp $ bodyResult bdy_tmp)
--               )
--               (resultBodyM [Constant $ blankPrimValue ptp])
--           ]
--     vs_bar <-
--       letTupExp (baseString vs ++ "_bar") $
--         Op $
--           Screma
--             n
--             [inds, vs]
--             (ScremaForm [] [] (Lambda [pj, pv] lam_bar [eltp]))
--     zipWithM_ updateAdj [vs] vs_bar
--   where
--     mkLamAddI64 = do
--       pab <- zipWithM newParam ["a", "b"] [Prim int64, Prim int64]
--       let [a, b] = map paramName pab
--       let addop = Add Int64 OverflowUndef
--       lam_bdy <- runBodyBuilder . localScope (scopeOfLParams pab) $ do
--         r <- letSubExp "r" $ BasicOp $ BinOp addop (Var a) (Var b)
--         resultBodyM [r]
--       return $ Lambda pab lam_bdy [Prim int64]

-- General case
diffHist vjops pat@(Pat [pe]) _aux soac m
  | (Hist n [inds, vs] hist_op bucket_fun) <- soac,
    -- Call from SOAC.hs should always call this fun with identity fun, but just to be safe.
    True <- isIdentityLambda bucket_fun,
    [HistOp shape _rf [orig_dst] nes f] <- hist_op,
    -- len(orig_hist)
    [t] <- lambdaReturnType f,
    [histDim] <- shapeDims shape = do
      let int64One  = Constant $ IntValue $ Int64Value 1
      let int64Zero = Constant $ IntValue $ Int64Value 0
      let int64Neg  = Constant $ IntValue $ Int64Value (-1)
      
      ---- (inds', iot') = Filter (inds, iot) w.r.t. inds. Remove those out of bounds of 0 - len(orig_dst)
      
      -- flags = map (\ind -> if 0 <= ind <= histDim then 1 else 0 inds
      ind_param <- newParam "ind" $ Prim int64
      pred_body <- runBodyBuilder . localScope (scopeOfLParams [ind_param]) $
        eBody
          [ eIf -- if ind > 0 then 0 else ...
            (eCmpOp (CmpSlt Int64) (eParam ind_param) (eSubExp int64Zero) )
            (eBody [eSubExp $ int64Zero])
            (eBody
              [
                eIf -- if histDim > ind then 0 else 1
                (eCmpOp (CmpSlt Int64) (eSubExp histDim) (eParam ind_param) )
                (eBody [eSubExp $ int64Zero])
                (eBody [eSubExp $ int64One])
              ])
          
          ]
      let pred_lambda = Lambda [ind_param] pred_body [Prim int64]
      flags <- letExp "flags" $ Op $ Screma n [inds] $ ScremaForm [][] pred_lambda

      -- flag_scanned = scan (+) 0 flags
      add_lambda_i64 <- addLambda (Prim int64)
      scan_soac <- scanSOAC [Scan add_lambda_i64 [intConst Int64 0]]
      flags_scanned <- letExp "flag_scanned" $ Op $ Screma n [flags] scan_soac

      -- n' = last flags_scanned
      lastElem <- letSubExp "lastElem" $ BasicOp $ BinOp (Sub Int64 OverflowUndef) n (int64One)
      n' <- letSubExp "new_length" $ BasicOp $ Index flags_scanned (fullSlice (Prim int64) [DimFix lastElem])
    
      -- new_inds = map (\(flag, flag_scan) -> if flag == 1 then flag_scan - 1 else -1)
      flag <- newParam "flag" $ Prim int64
      flag_scan <- newParam "flag_scan" $ Prim int64
      new_inds_body <- runBodyBuilder . localScope (scopeOfLParams [flag, flag_scan]) $
        
        eBody
        [ eIf -- if flag == 1
          (eCmpOp (CmpEq int64) (eParam flag) (eSubExp (int64One)))
          (eBody [eBinOp (Sub Int64 OverflowUndef) (eSubExp $ Var $ paramName flag_scan) (eSubExp $ int64One)])
          (eBody [eSubExp $ int64Neg])  
        ]
      let new_inds_lambda = Lambda [flag, flag_scan] new_inds_body [Prim int64]
      new_inds <- letExp "new_inds" $ Op $ Screma n [flags, flags_scanned] $ ScremaForm [][] new_inds_lambda
          
      -- new_indexes = scatter (Scratch int n') new_inds (iota n)     
      f'' <- mkIdentityLambda [Prim int64, Prim int64]
      orig_indexes <- letExp "orig_indexes" $ BasicOp $ Iota n (intConst Int64 0) (intConst Int64 1) Int64
      indexes_dst <- letExp "indexes_dst" $ BasicOp $ Scratch int64 [n']
      new_indexes <- letExp "new_indexes" $ Op $ Scatter n [new_inds, orig_indexes] f'' [(Shape [n'], 1, indexes_dst)]

      -- new_bins = map (\i -> bins[i]) indexes
      i <- newParam "i" $ Prim int64
      new_bins_body <- runBodyBuilder . localScope (scopeOfLParams [i]) $ do
        body <- letSubExp "body" $ BasicOp $ Index inds (fullSlice (Prim int64) [DimFix (Var (paramName i))])     
        resultBodyM [body]
      let new_bins_lambda = Lambda [i] new_bins_body [Prim int64]
      new_bins <- letExp "new_bins" $ Op $ Screma n' [new_indexes] $ ScremaForm [][] new_bins_lambda

      
      ---- Radix sort (new_bins, new_indexes) w.r.t. new_bins.
      -- [sorted_is, sorted_bins] = 
      --   loop over [new_indexes, new_bins] for i < 63 do 
      --     bits = map (\ind_x -> (ind_x >> i) & 1) new_bins
      --     newidx = partition2 bits (iota n')
      --     [map(\i -> new_indexes[i]) newidx, map(\i -> new_bins[i]) newidx]
      i2 <- newVName "i2"

      indexesForLoop <- newVName "new_indexes_rebound"
      new_indexes_cpy <- letExp (baseString new_indexes ++ "_copyLoop") $ BasicOp $ Copy new_indexes
      new_indexes_type <- lookupType new_indexes
      let isDeclTypeInds = toDecl new_indexes_type Unique
      let paramIndexes = Param mempty indexesForLoop isDeclTypeInds
      
      binsForLoop <- newVName "new_bins_rebound"
      new_bins_cpy <- letExp (baseString new_bins ++ "_copyLoop") $ BasicOp $ Copy new_bins
      new_bins_type <- lookupType new_bins
      let isDeclTypeBins = toDecl new_bins_type Unique
      let paramBins = Param mempty binsForLoop isDeclTypeBins
      
      let loop_vars = [(paramIndexes, Var new_indexes_cpy),(paramBins, Var new_bins_cpy)]
      
      -- bound = log2ceiling(w) (inner hist size aka number of bins)
      let bound = Constant $ IntValue $ intValue Int64 (63::Integer) -- Set to 63 since the most significant bit of signed int is negative numbers, which have been filtered out.

      ((idxres, binsres), stms) <- runBuilderT' . localScope (scopeOfFParams [paramIndexes, paramBins]) $ do
        -- bits = map (\ind_x -> (ind_x >> digit_n) & 1) ind
        ind_x <- newParam "ind_x" $ Prim int64
        bits_map_bdy <- runBodyBuilder . localScope (scopeOfLParams [ind_x]) $
          eBody
          [
            eBinOp (And Int64)
              (eBinOp (LShr Int64) (eParam ind_x) (eSubExp $ Var i2))
              (eSubExp $ int64One)
          ]
        let bits_map_lam = Lambda [ind_x] bits_map_bdy [Prim int64]
        bits <- letExp "bits" $ Op $ Screma n' [binsForLoop] (ScremaForm [] [] bits_map_lam)

        -- Partition iota to get the new indices to scatter bins and inds by
        temp_iota <- letExp "temp_iota" $ BasicOp $ Iota n' int64Zero int64One Int64
        scatter_soac <- partition2Maker n' bits temp_iota
        partitionedidx <- letExp (baseString inds ++ "_scattered") $ Op $ scatter_soac

        inner_indx_idx <- newParam "inner_indexes_idx" $ Prim int64
        inner_indx_bdy <- runBodyBuilder . localScope (scopeOfLParams [inner_indx_idx]) $ do
          tmp <- letSubExp "indexes_body" $ BasicOp $ Index (paramName paramIndexes) (fullSlice (Prim int64) [DimFix (Var (paramName inner_indx_idx))])
          resultBodyM [tmp]
        let inner_indx_lambda = Lambda [inner_indx_idx] inner_indx_bdy [Prim int64]
        inner_new_indexes <- letSubExp "new_indexes" $ Op $ Screma n' [partitionedidx] $ ScremaForm [][] inner_indx_lambda

        inner_bins_idx <- newParam "inner_indexes_idx" $ Prim int64
        inner_bins_bdy <- runBodyBuilder . localScope (scopeOfLParams [inner_bins_idx]) $ do
          tmp <- letSubExp "indexes_body" $ BasicOp $ Index (paramName paramBins) (fullSlice (Prim int64) [DimFix (Var (paramName inner_bins_idx))])
          resultBodyM [tmp]
        let inner_bins_lambda = Lambda [inner_bins_idx] inner_bins_bdy [Prim int64]
        inner_new_bins <- letSubExp "new_bins" $ Op $ Screma n' [partitionedidx] $ ScremaForm [][] inner_bins_lambda

        return (inner_new_indexes, inner_new_bins)

      loop_bdy <- mkBodyM stms [subExpRes idxres,subExpRes binsres]
      loop_res <- letTupExp "sorted_is_bins" $ DoLoop loop_vars (ForLoop i2 Int64 bound []) loop_bdy
      let [sorted_is, sorted_bins] = loop_res


      -- Collect sorted values
      -- sorted_vals = map(\i -> vs[i]) sorted_is
      val_idx <- newParam "val_idx" $ Prim int64
      sorted_vals_body <- runBodyBuilder . localScope (scopeOfLParams [val_idx]) $ do
        body <- letSubExp "body" $ BasicOp $ Index vs (fullSlice (Prim int64) [DimFix (Var (paramName val_idx))])     
        resultBodyM [body]
      let sorted_vals_lambda = Lambda [val_idx] sorted_vals_body [t]
      sorted_vals <- letExp "sorted_vals" $ Op $ Screma n' [sorted_is] $ ScremaForm [][] sorted_vals_lambda

      let trueSE  = Constant $ IntValue $ intValue Int8 (1 :: Integer)
      let falseSE = Constant $ IntValue $ intValue Int8 (0 :: Integer)

      -- map (\(index) -> if sorted_bins[index] == sorted_bins[index-1] then 0 else 1) iota n'
      -- Make flag array
      iota_n' <- letExp "iota_n'" $ BasicOp $ Iota n' (intConst Int64 0) (intConst Int64 1) Int64
      bin <- newParam "bin" $ Prim int64
      index <- newParam "iot_n'" $ Prim $ int64
      mk_flag_body <- runBodyBuilder . localScope (scopeOfLParams [bin, index]) $ do
        
        idx_minus_one <- letSubExp "idx_minus_one" $ BasicOp $ BinOp (Sub Int64 OverflowUndef) (Var $ paramName index) (intConst Int64 1)
        prev_elem <- letExp "prev_elem" $ BasicOp $ Index sorted_bins (fullSlice (Prim int64) [DimFix idx_minus_one]) 
        
        let firstElem =
              eCmpOp
                (CmpEq $ IntType Int64)
                (eSubExp $ Var $ paramName index)
                (eSubExp $ intConst Int64 0)

        let elemEq =
              eCmpOp
                (CmpEq $ IntType Int64)
                (eSubExp $ Var prev_elem)
                (eSubExp $ Var $ paramName bin)

        eBody
          [
            eIf
              firstElem
              (resultBodyM $ [trueSE])
              (eBody
                [
                  eIf
                    elemEq
                    (resultBodyM $ [falseSE])
                    (resultBodyM $ [trueSE])
                ])
          ]
      let mk_flag_lambda = Lambda [bin, index] mk_flag_body [Prim $ IntType Int8]
      final_flags <- letExp "final_flags" $ Op $ Screma n' [sorted_bins, iota_n'] $ ScremaForm [][] mk_flag_lambda


      ---- Forward segmented exlusive scan in one array, reverse segmented exlusive scan in another.
      seg_scan_exc <- mkSegScanExc f nes n' sorted_vals final_flags
      fwd_scan <- letTupExp "fwd_scan" $ Op seg_scan_exc
      let [_, lis] = fwd_scan

      ---- Reverse segmented exculsive scan. Reverse flags and vals.
      -- rev_vals = reverse sorted_vals
      rev_vals <- eReverse sorted_vals
      -- final_flags_rev = reverse final_flags
      final_flags_rev <- eReverse final_flags

      -- Need to fix flags after reversing
      -- rev_flags = map (\ind -> if ind == 0 then 1 else rev[ind-1])
      i' <- newParam "i" $ Prim int64
      rev_flags_body <- runBodyBuilder . localScope (scopeOfLParams [i']) $ do
        idx_minus_one <- letSubExp "idx_minus_one" $ BasicOp $ BinOp (Sub Int64 OverflowUndef) (Var $ paramName i') (intConst Int64 1)
        prev_elem <- letSubExp "prev_elem" $ BasicOp $ Index final_flags_rev (fullSlice (Prim int64) [DimFix idx_minus_one]) 
        
        let firstElem =
              eCmpOp
                (CmpEq $ IntType Int64)
                (eSubExp $ Var $ paramName i')
                (eSubExp $ intConst Int64 0)

        eBody
          [
            eIf
              firstElem
              (resultBodyM [trueSE])
              (resultBodyM [prev_elem])
          ]
      let rev_flags_lambda = Lambda [i'] rev_flags_body [Prim int8]
      rev_flags <- letExp "rev_flags" $ Op $ Screma n' [iota_n'] $ ScremaForm [][] rev_flags_lambda

      -- Run segmented scan on reversed arrays.
      rev_seg_scan_exc <- mkSegScanExc f nes n' rev_vals rev_flags
      rev_scan <- letTupExp "rev_scan" $ Op rev_seg_scan_exc
      let [_, ris_rev] = rev_scan
      ris <- eReverse ris_rev

      -- Get index of the end of each segment
      --seg_end_idx = map (\i, bin -> if i == n'-1
      --                              then bin
      --                              else if final_flags[i+1] == 1 
      --                                   then bin
      --                                   else -1
      --                   ) (iota n') sorted_bins

      i'' <- newParam "i''" $ Prim int64
      current_bin <- newParam "current_bin" $ Prim int64
      seg_end_idx_body <- runBodyBuilder . localScope (scopeOfLParams [i'', current_bin]) $ do
        idx_plus_one <- letSubExp "idx_plus_one" $ BasicOp $ BinOp (Add Int64 OverflowUndef) (Var $ paramName i'') (intConst Int64 1)
        lastElemIdx <- letExp "lastElemIdx" $ BasicOp $ BinOp (Sub Int64 OverflowUndef) (n') (intConst Int64 1)

        let isLastElem =
              eCmpOp
                (CmpEq $ IntType Int64)
                (eSubExp $ Var $ paramName i'')
                (eSubExp $ Var $ lastElemIdx)

        eBody
          [
            eIf
            isLastElem
            (resultBodyM $ [Var $ paramName current_bin])
            (eBody
              [
                eIf
                  ( do
                      next_elem <- letExp "next_elem" $ BasicOp $ Index final_flags (fullSlice (Prim int64) [DimFix idx_plus_one])
                      (eCmpOp
                        (CmpEq $ IntType Int8)
                        (eSubExp $ Var next_elem)
                        (eSubExp $ Constant $ IntValue $ Int8Value 1))
                  )
                (resultBodyM [Var $ paramName current_bin])
                (resultBodyM [Constant $ IntValue $ Int64Value (-1)])
              ]
            )
          ]

      let seg_end_idx_lam = Lambda [i'', current_bin] seg_end_idx_body [Prim int64]
      seg_end_idx <- letExp "seg_end_idx" $ Op $ Screma n' [iota_n', sorted_bins] $ ScremaForm [][] seg_end_idx_lam

      --bin_lst_lis   = scatter (replicate ne (len hist_orig)) seg_end_idx lis
      bin_last_lis_dst <- letExp "bin_last_lis_dst" $ BasicOp $ Replicate shape (head nes)
      f''' <- mkIdentityLambda [Prim int64 , t]
      bin_last_lis <- letExp "bin_last_lis" $ Op $ Scatter n' [seg_end_idx, lis] f''' [(shape, 1, bin_last_lis_dst)]

      -- lis was exc-scan, so we need the last element aswell.
      -- bin_last_v_dst = scatter (replicate ne (len hist_orig)) seg_end_idx sorted_vals
      bin_last_v_dst <- letExp "bin_last_v_dst" $ BasicOp $ Replicate shape (head nes)
      f'''' <- mkIdentityLambda [Prim int64 , t]
      bin_last_v <- letExp "bin_last_v" $ Op $ Scatter n' [seg_end_idx, sorted_vals] f'''' [(shape, 1, bin_last_v_dst)]

      -- Temp histogram of only our input values.
      -- hist' = map2 lam bin_last_lis bin_last_v
      lis_param <- mapM (newParam "lis_param") [t]
      v_param   <- mapM (newParam "v_param") [t]

      -- rename input lambda
      op_lam <- renameLambda f
      op <- mkLambda (lis_param ++ v_param) $ do
        eLambda op_lam (map (eSubExp . Var . paramName) (lis_param ++ v_param))
      
      hist_temp <- letExp "hist_temp" $ Op $ Screma histDim [bin_last_lis, bin_last_v] $ ScremaForm [][] op

      -- Temp histogram of only our input values.
      -- hist' = map2 lam bin_last_lis bin_last_v
      orig_param <- mapM (newParam "orig_param") [t]
      temp_param <- mapM (newParam "temp_param") [t]

      -- rename input lambda
      op_lam2 <- renameLambda f
      op2 <- mkLambda (orig_param ++ temp_param) $ do
        eLambda op_lam2 (map (eSubExp . Var . paramName) (orig_param ++ temp_param))

      hist_res <- letExp "hist_res" $ Op $ Screma histDim [orig_dst, hist_temp] $ ScremaForm [][] op2
      
      -- Bind resulting histogram to the pattern.
      letBind pat $ BasicOp $ SubExp $ Var hist_res

      m
       


      -- Lookup adjoint of histogram
      hist_res_bar <- lookupAdjVal $ patElemName pe

      -- Rename original function
      hist_temp_lam <- renameLambda f
      hist_orig_lam <- renameLambda f

      -- Lift lambda to compute differential wrt. first or second element.
      hist_orig_bar_temp_lambda <- mkScanAdjointLam vjops hist_orig_lam WrtFirst
      hist_temp_bar_temp_lambda <- mkScanAdjointLam vjops hist_temp_lam WrtSecond
      
      -- Lambda for multiplying hist_res_bar onto result of differentiation 
      let mulOp = getMulOp t
      mul_hist_orig_res_adj <- mkSimpleLambda "orig_adj" "res_adj" mulOp t
      mul_hist_temp_res_adj <- mkSimpleLambda "temp_adj" "res_adj" mulOp t

      -- Compute adjoint of each bin of each histogram (original and added values).
      hist_orig_bar_temp <- letExp "hist_orig_bar_temp" $ Op $ Screma histDim [orig_dst, hist_temp] $ ScremaForm [][] hist_orig_bar_temp_lambda
      hist_orig_bar      <- letExp "hist_orig_bar" $ Op $ Screma histDim [hist_orig_bar_temp, hist_res_bar] $ ScremaForm [][] mul_hist_orig_res_adj
      
      hist_temp_bar_temp <- letExp "hist_temp_bar_temp" $ Op $ Screma histDim [orig_dst, hist_temp] $ ScremaForm [][] hist_temp_bar_temp_lambda
      hist_temp_bar      <- letExp "hist_temp_bar" $ Op $ Screma histDim [hist_temp_bar_temp, hist_res_bar] $ ScremaForm [][] mul_hist_temp_res_adj

      -- Set adjoint of orig_dst for future use
      insAdj orig_dst hist_orig_bar

      -- Now for adjoint of vs
      -- For each bin in sorted_bins we fetch the adjoint of the corresponding bucket in hist_temp_bar
      -- hist_temp_bar_repl = map (\bin -> hist_temp_bar[bin]) sorted_bins
      sorted_bin_param <- newParam "sorted_bin_p" $ Prim int64
      hist_temp_bar_repl_body <- runBodyBuilder . localScope (scopeOfLParams [sorted_bin_param]) $ do
        hist_temp_adj <- letSubExp "hist_temp_adj" $ BasicOp $ Index hist_temp_bar (fullSlice (Prim int64) [DimFix (Var (paramName sorted_bin_param))])     
        resultBodyM [hist_temp_adj]
      let hist_temp_bar_repl_lambda = Lambda [sorted_bin_param] hist_temp_bar_repl_body [t]
      hist_temp_bar_repl <- letExp "hist_temp_bar_repl" $ Op $ Screma n' [sorted_bins] $ ScremaForm [][] hist_temp_bar_repl_lambda

      -- We now use vjpMap to compute vs_bar
      (_, lam_adj) <- mkF f
      vjpMap vjops [AdjVal $ Var hist_temp_bar_repl] n' lam_adj [lis, sorted_vals, ris] -- Doesn't support lists

      -- We are only using values not sorted out. Need to add 0 for each value that was sorted out.
      -- Get adjoints of values with valid bins (computed by running vjpMap before)
      vs_bar_contrib_reordered <- lookupAdjVal sorted_vals
      -- Replicate array of 0's
      vs_bar_contrib_dst <- letExp "vs_bar_contrib_dst" $ BasicOp $ Replicate (Shape [n]) (getBaseAdj t)
      -- Scatter adjoints to 0-array.
      f''''' <- mkIdentityLambda [Prim int64, t]
      vs_bar_contrib <- letExp "vs_bar_contrib" $ Op $ Scatter n' [sorted_is, vs_bar_contrib_reordered] f''''' [(Shape [n], 1, vs_bar_contrib_dst)]
      -- Update the adjoint of vs to be vs_bar_contrib
      updateAdj vs vs_bar_contrib-- second value here is the contributions, currently not used because it has to be [n] and all we have is [new_length]



diffHist _ _ _ soac _ =
  error $ "Unsuported histogram: " ++ pretty soac
