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
import Futhark.Analysis.PrimExp.Convert
import Futhark.Builder
import Futhark.IR.SOACS
import Futhark.Tools
import Futhark.Transform.Rename

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

getBinOpMul :: PrimType -> BinOp
getBinOpMul (IntType x) = Mul x OverflowUndef
getBinOpMul (FloatType f) = FMul f
getBinOpMul _ = error "In getBinOpMul, Reduce_by_index.hs: input not supported"

withinBounds :: [(SubExp, VName)] -> TPrimExp Bool VName
withinBounds [] = TPrimExp $ ValueExp (BoolValue True)
withinBounds [(q, i)] = (le64 i .<. pe64 q) .&&. (pe64 (intConst Int64 (-1)) .<. le64 i)
withinBounds (qi : qis) = withinBounds [qi] .&&. withinBounds qis


genIdxLamBdy :: VName -> [(SubExp, Param Type)] -> Type -> ADM Body
genIdxLamBdy as wpis = genRecLamBdy as wpis []
  where
    genRecLamBdy :: VName -> [(SubExp, Param Type)] -> [Param Type] -> Type -> ADM Body
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
                  r <- letSubExp "r" $ BasicOp $ Index arr $ Slice $ map (DimFix . Var) inds
                  resultBodyM [r]
              )
              (resultBodyM [Constant $ blankPrimValue ptp])
          ]
    genRecLamBdy _ _ _ _ = error "In Reduce_by_index.hs, helper function genRecLamBdy, unreachable case reached!"

-- Pattern Matches special lambda cases:
--   plus, multiplication, min, max, which are all commutative.
-- Succeeds for (\ x y -> x binop y) or (\x y -> y binop x).
isSpecOpLam :: (BinOp -> Maybe BinOp) -> Lambda -> Maybe BinOp
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

isAddTowLam :: Lambda -> Maybe BinOp
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

isMulLam :: Lambda -> Maybe BinOp
isMulLam = isSpecOpLam isMulOp
  where
    isMulOp bop@(Mul _ _) = Just bop
    isMulOp bop@(FMul _) = Just bop
    isMulOp _ = Nothing

isMinMaxLam :: Lambda -> Maybe BinOp
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
mkMinMaxIndLam :: PrimType -> BinOp -> ADM Lambda
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

helperMulOp1 :: PrimType -> BinOp -> ADM (Lambda, Lambda)
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

helperMulOp3 :: PrimType -> BinOp -> VName -> VName -> Param Type -> VName -> ADM Body
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

-- Lift a lambda to produce an exlusive segmented scan operator.
mkSegScanExc :: Lambda -> SubExp -> SubExp -> VName -> VName -> ADM (SOAC SOACS) 
mkSegScanExc lam ne n vals flags = do
  -- Get lambda return type
  let rt = lambdaReturnType lam
  v1 <- mapM (newParam "v1") rt
  v2 <- mapM (newParam "v2") rt
  f1 <- newParam "f1" $ Prim int8
  f2 <- newParam "f2" $ Prim int8
  let params = f1 : f2 : (v1 ++ v2)
  -- let oneSubExp = Constant $ IntValue $ intValue Int64 1
  
  scan_body <- runBodyBuilder . localScope (scopeOfLParams params) $ do
    -- f = f1 || f2
    f <- letSubExp "f" $ BasicOp $ BinOp (Or Int8 ) (Var $ paramName f1) (Var $ paramName f2)
    v <- letSubExp "v" $ Op $
      Screma (intConst Int64 1) (map paramName $ v1++v2) (mapSOAC lam)
    -- v = if f2 then ne else (lam v1 v2) 
    let f2_check =
          eCmpOp
            (CmpEq $ IntType Int8)
            (eSubExp $ Var $ paramName f2)
            (eSubExp $ intConst Int8 0)
    eBody
      [
        eIf
          f2_check
          (resultBodyM $ [f, ne])
          (resultBodyM $ [f, v])
      ]
  let scan_lambda = Lambda params scan_body (rt ++ [Prim int64])
  scan_soac <- scanSOAC [Scan scan_lambda [ne, intConst Int64 0]]
  return $ Screma n [vals, flags] scan_soac

-- partion2Maker - Takes flag array and values and creates a scatter SOAC
--                  which corresponds to the partition2 of the inputs
-- partition2Maker size flags values = 
partition2Maker ::  SubExp -> VName -> VName -> ADM (SOAC SOACS)
partition2Maker n bits xs = do
  
  let bitType = int64
  ptp <- lookupType xs
  let zeroSubExp = Constant $ IntValue $ intValue Int64 0
  let oneSubExp = Constant $ IntValue $ intValue Int64 1
  let minusOneSubExp = Constant $ IntValue $ intValue Int64 1

  -- let bits_inv = map (\b -> 1 - b) bits
  bit_x <- newParam "bit_x" $ Prim bitType
  bits_inv_map_bdy <- runBodyBuilder . localScope (scopeOfLParams [bit_x]) $ do
    eBody
      [
        eBinOp (Sub Int64 OverflowUndef)
        (eSubExp $ Constant $ IntValue $ intValue Int64 1)
        (eParam bit_x)
      ]
  let bits_inv_map_lam = Lambda [bit_x] bits_inv_map_bdy [Prim bitType]
  bits_inv <- letExp "bits_inv" $ Op $ Screma n [bits] (ScremaForm [] [] bits_inv_map_lam)

  -- let ps0 = scan (+) 0 (bits_inv)
    -- * Generalize this part so we can use it twice without geting "bound twice" error
  ps0_x <- newParam "ps0_x" $ Prim bitType
  ps0_y <- newParam "ps0_y" $ Prim bitType
  ps0_scanlam_bdy <- runBodyBuilder . localScope (scopeOfLParams [ps0_x, ps0_y]) $ do
    eBody
      [
        eBinOp (Add Int64 OverflowUndef)
        (eParam ps0_x)
        (eParam ps0_y)
      ]
  let ps0_scanlam = Lambda [ps0_x, ps0_y] ps0_scanlam_bdy [Prim bitType]
  let ps0_scan = Scan ps0_scanlam [Constant $ IntValue $ intValue Int64 0]
    -- *
  f' <- mkIdentityLambda [Prim bitType]
  ps0 <- letExp "ps0" $ Op $ Screma n [bits_inv] (ScremaForm [ps0_scan] [] f')

  -- let ps0_clean = map2 (*) bits_inv ps0 
  ps0clean_bitinv <- newParam "ps0clean_bitinv" $ Prim bitType
  ps0clean_ps0 <- newParam "ps0clean_ps0" $ Prim bitType
  ps0clean_lam_bdy <- runBodyBuilder . localScope (scopeOfLParams [ps0clean_bitinv, ps0clean_ps0]) $ do
    eBody
      [
        eBinOp (Mul Int64 OverflowUndef)
        (eParam ps0clean_bitinv)
        (eParam ps0clean_ps0)
      ]
  let ps0clean_lam = Lambda [ps0clean_bitinv, ps0clean_ps0] ps0clean_lam_bdy [Prim bitType]
  ps0clean <- letExp "ps0_clean" $ Op $ Screma n [bits_inv, ps0] (ScremaForm [] [] ps0clean_lam)

  -- let ps1 = scan (+) 0 bits
    -- * Generalize this part so we can use it twice without geting "bound twice" error
  ps1_x <- newParam "ps1_x" $ Prim bitType
  ps1_y <- newParam "ps1_y" $ Prim bitType
  ps1_scanlam_bdy <- runBodyBuilder . localScope (scopeOfLParams [ps1_x, ps1_y]) $ do
    eBody
      [
        eBinOp (Add Int64 OverflowUndef)
        (eParam ps1_x)
        (eParam ps1_y)
      ]
  let ps1_scanlam = Lambda [ps1_x, ps1_y] ps1_scanlam_bdy [Prim bitType]
  let ps1_scan = Scan ps1_scanlam [Constant $ IntValue $ intValue Int64 0]
    -- *
  f'' <- mkIdentityLambda [Prim bitType]
  ps1 <- letExp "ps1" $ Op $ Screma n [bits] (ScremaForm [ps1_scan] [] f'')


  -- let ps0_offset = reduce (+) 0 bits_inv
    -- * Generalize this part so we can use it twice without geting "bound twice" error
  ps0off_x <- newParam "ps0off_x" $ Prim bitType
  ps0off_y <- newParam "ps0off_y" $ Prim bitType
  ps0off_redlam_bdy <- runBodyBuilder . localScope (scopeOfLParams [ps0off_x, ps0off_y]) $ do
    eBody
      [
        eBinOp (Add Int64 OverflowUndef)
        (eParam ps0off_x)
        (eParam ps0off_y)
      ]
  let ps0off_redlam = Lambda [ps0off_x, ps0off_y] ps0off_redlam_bdy [Prim bitType]
    -- *
  ps0off_red <- reduceSOAC [Reduce Commutative ps0off_redlam [intConst Int64 0]]
  ps0off <- letExp "ps0off" $ Op $ Screma n [bits_inv] ps0off_red


  -- let ps1_clean = map (+ps0_offset) ps1
  ps1clean_x <- newParam "ps1clean_x" $ Prim bitType
  ps1clean_lam_bdy <- runBodyBuilder . localScope (scopeOfLParams [ps1clean_x]) $ do
    eBody
      [
        eBinOp (Add Int64 OverflowUndef)
        (eParam ps1clean_x)
        (eSubExp $ Var ps0off)
      ]
  let ps1clean_lam = Lambda [ps1clean_x] ps1clean_lam_bdy [Prim bitType]
  ps1clean <- letExp "ps1clean" $ Op $ Screma n [ps1] (ScremaForm [] [] ps1clean_lam)

  -- let ps0_clean = map2 (*) bits_inv ps0 
  ps1clean'_bit <- newParam "ps1cleanprim_bit" $ Prim bitType
  ps1clean'_ps1clean <- newParam "ps1cleanprim_ps1clean" $ Prim bitType
  ps1clean'_lam_bdy <- runBodyBuilder . localScope (scopeOfLParams [ps1clean'_bit, ps1clean'_ps1clean]) $ do
    eBody
      [
        eBinOp (Mul Int64 OverflowUndef)
        (eParam ps1clean'_bit)
        (eParam ps1clean'_ps1clean)
      ]
  let ps1clean'_lam = Lambda [ps1clean'_bit, ps1clean'_ps1clean] ps1clean'_lam_bdy [Prim bitType]
  ps1clean' <- letExp "ps1_cleanprim" $ Op $ Screma n [bits, ps1clean] (ScremaForm [] [] ps1clean'_lam)

  -- let ps = map2 (+) ps0_clean ps1_clean'
  ps_ps0clean <- newParam "ps_ps0clean" $ Prim bitType
  ps_ps1clean' <- newParam "ps_ps1cleanprim" $ Prim bitType
  ps_lam_bdy <- runBodyBuilder . localScope (scopeOfLParams [ps_ps0clean, ps_ps1clean']) $ do
    eBody
      [
        eBinOp (Mul Int64 OverflowUndef)
        (eParam ps_ps0clean)
        (eParam ps_ps1clean')
      ]
  let ps_lam = Lambda [ps_ps0clean, ps_ps1clean'] ps_lam_bdy [Prim bitType]
  ps <- letExp "ps" $ Op $ Screma n [ps0clean, ps1clean'] (ScremaForm [] [] ps_lam)


  -- let ps_actual = map (-1) ps
  psactual_x <- newParam "psactual_x" $ Prim bitType
  psactual_lam_bdy <- runBodyBuilder . localScope (scopeOfLParams [psactual_x]) $ do
    eBody
      [
        eBinOp (Sub Int64 OverflowUndef)
        (eParam psactual_x)
        (eSubExp $ minusOneSubExp)
      ]
  let psactual_lam = Lambda [psactual_x] psactual_lam_bdy [Prim bitType]
  psactual <- letExp "psactual" $ Op $ Screma n [ps] (ScremaForm [] [] psactual_lam)
  
  -- let scatter_inds = scatter inds ps_actual inds
  f''' <- mkIdentityLambda [Prim int64, Prim int64]
  xs_cpy <- letExp (baseString xs ++ "_copy") $ BasicOp $ Copy xs
  return $ Scatter n [psactual, xs] f''' [(Shape [n], 1, xs_cpy)]

diffHist :: VjpOps -> Pat -> StmAux() -> SOAC SOACS -> ADM () -> ADM ()
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
    pind <- newParam "ind" $ Prim int64
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

diffHist _vjops (Pat [pe]) aux soac m 
  | (Hist n [inds, vs] hist_mul bucket_fun) <- soac,
    True <- isIdentityLambda bucket_fun,
    [HistOp shape rf [orig_dst] [ne] mul_lam] <- hist_mul,
    Just mulop <- isMulLam mul_lam,
    [eltp] <- lambdaReturnType mul_lam,
    Prim ptp <- eltp,
    [shapedim] <- shapeDims shape = do
    -- starts here:
    let pe_tp = patElemDec pe
    (map_lam, _) <- helperMulOp1 ptp mulop
    vs_lift <- letTupExp "nzel_zrct" $ Op $ Screma n [vs] (ScremaForm [] [] map_lam)
    let [nz_vs, one_zrs] = vs_lift
    zr_counts0 <- letExp "zr_cts" $ BasicOp $ Replicate shape (intConst Int64 0)
    nz_prods0 <- letExp "nz_prd" $ BasicOp $ Replicate shape ne
    nz_prods <- newVName "non_zero_prod"
    zr_counts <- newVName "zero_count"
    lam_add <- mkLamAddI64
    let hist_zrn = HistOp shape rf [zr_counts0] [intConst Int64 0] lam_add
    let hist_nzp = HistOp shape rf [nz_prods0] [ne] mul_lam
    f' <- mkIdentityLambda [Prim int64, Prim int64, eltp, Prim int64]
    let soac_pat =
          Pat
            [ PatElem nz_prods pe_tp,
              PatElem zr_counts $
              arrayOf (Prim int64) shape NoUniqueness
            ]
    let soac_exp = Op $ Hist n [inds, inds, nz_vs, one_zrs] [hist_nzp, hist_zrn] f'
    auxing aux $ letBind soac_pat soac_exp
    -- construct the histo result:
    res_part <- newVName "res_part"
    ps2 <- zipWithM newParam ["nz_pr", "zr_ct"] [eltp, Prim int64]
    let [nz_prod, zr_count] = map paramName ps2
    if_stms <- helperMulOp2 ptp nz_prod zr_count res_part
    lam_bdy_2 <- runBodyBuilder . localScope (scopeOfLParams ps2) $ do
      addStms if_stms
      resultBodyM [Var res_part]
    h_part <-
      letExp "hist_part" $
        Op $
          Screma
            shapedim
            [nz_prods, zr_counts]
            (ScremaForm [] [] (Lambda ps2 lam_bdy_2 [eltp]))
    ps3 <- zipWithM newParam ["h_orig", "h_part"] [eltp, eltp]
    let [ph_orig, ph_part] = map paramName ps3
    lam_pe_bdy <- runBodyBuilder . localScope (scopeOfLParams ps3) $ do
      r <- letSubExp "res" $ BasicOp $ BinOp mulop (Var ph_orig) (Var ph_part)
      resultBodyM [r]
    auxing aux $
      letBind (Pat [pe]) $
        Op $
          Screma
            shapedim
            [orig_dst, h_part]
            (ScremaForm [] [] (Lambda ps3 lam_pe_bdy [eltp]))
    m
    -- reverse trace
    pe_bar <- lookupAdjVal $ patElemName pe
    -- updates the orig_dst with its proper bar
    mul_lam' <- renameLambda mul_lam
    orig_bar <-
      letTupExp (baseString orig_dst ++ "_bar") $
        Op $
          Screma
            shapedim
            [h_part, pe_bar]
            (ScremaForm [] [] mul_lam')
    zipWithM_ updateAdj [orig_dst] orig_bar
    -- updates the partial histo result with its proper bar
    mul_lam'' <- renameLambda mul_lam
    part_bars <-
      letTupExp (baseString h_part ++ "_bar") $
        Op $
          Screma
            shapedim
            [orig_dst, pe_bar]
            (ScremaForm [] [] mul_lam'')
    let [part_bar] = part_bars
    -- add the contributions to each array element
    pj <- newParam "j" (Prim int64)
    pv <- newParam "v" eltp
    let j = paramName pj
    ((zr_cts, pr_bar, nz_prd), tmp_stms) <- runBuilderT' . localScope (scopeOfLParams [pj, pv]) $ do
      zr_cts <- letExp "zr_cts" $ BasicOp $ Index zr_counts $ fullSlice eltp [DimFix (Var j)]
      pr_bar <- letExp "pr_bar" $ BasicOp $ Index part_bar $ fullSlice eltp [DimFix (Var j)]
      nz_prd <- letExp "nz_prd" $ BasicOp $ Index nz_prods $ Slice [DimFix (Var j)]
      return (zr_cts, pr_bar, nz_prd)
    bdy_tmp <- helperMulOp3 ptp mulop nz_prd zr_cts pv pr_bar
    lam_bar <-
      runBodyBuilder . localScope (scopeOfLParams [pj, pv]) $
        eBody
          [ eIf
              (toExp $ withinBounds [(shapedim, j)])
              ( do
                  addStms (tmp_stms <> bodyStms bdy_tmp)
                  resultBodyM (map resSubExp $ bodyResult bdy_tmp)
              )
              (resultBodyM [Constant $ blankPrimValue ptp])
          ]
    vs_bar <-
      letTupExp (baseString vs ++ "_bar") $
        Op $
          Screma
            n
            [inds, vs]
            (ScremaForm [] [] (Lambda [pj, pv] lam_bar [eltp]))
    zipWithM_ updateAdj [vs] vs_bar
  where
    mkLamAddI64 = do
      pab <- zipWithM newParam ["a", "b"] [Prim int64, Prim int64]
      let [a, b] = map paramName pab
      let addop = Add Int64 OverflowUndef
      lam_bdy <- runBodyBuilder . localScope (scopeOfLParams pab) $ do
        r <- letSubExp "r" $ BasicOp $ BinOp addop (Var a) (Var b)
        resultBodyM [r]
      return $ Lambda pab lam_bdy [Prim int64]

-- General case
diffHist vjops pat@(Pat [pe]) aux soac m
  | (Hist n [inds, vs] hist_op bucket_fun) <- soac,
    True <- isIdentityLambda bucket_fun,
    [HistOp shape rf [orig_dst] [ne] f] <- hist_op,
    [eltp] <- lambdaReturnType f,
    Prim ptp <- eltp,
    -- len(orig_hist)
    [histDim] <- shapeDims shape = do
      let int64One  = IntValue $ Int64Value 1
      let int64Zero = IntValue $ Int64Value 0
      let int64Neg  = IntValue $ Int64Value (-1)
      
      ---- (inds', iot') = Filter (inds, iot) w.r.t. inds. Remove those out of bounds of 0 - len(orig_dst)
      
      -- flags = map (\ind -> if 0 <= ind <= histDim then 1 else 0 inds
      ind_param <- newParam "ind" $ Prim int64
      pred_body <- runBodyBuilder . localScope (scopeOfLParams [ind_param]) $
        eBody
          [ eIf -- if 0 <= ind
            (eCmpOp (CmpSle Int64) (eSubExp (Constant int64Zero)) (eParam ind_param) )
            (eBody [eSubExp $ Constant int64Zero])
            (eBody
              [
                eIf -- if ind > histDiam
                (eCmpOp (CmpSlt Int64) (eSubExp histDim) (eParam ind_param) )
                (eBody [eSubExp $ Constant int64Zero])
                (eBody [eSubExp $ Constant int64One])
              ])
          
          ]
      let pred_lambda = Lambda [ind_param] pred_body [Prim int64]
      flags <- letExp "flags" $ Op $ Screma n [inds] $ ScremaForm [][] pred_lambda

      -- flag_scanned = scan (+) 0 flags
      add_lambda_i64 <- addLambda (Prim int64)
      scan_soac <- scanSOAC [Scan add_lambda_i64 [intConst Int64 0]]
      flags_scanned <- letExp "flag_scanned" $ Op $ Screma n [flags] scan_soac

      -- n' = last flags_scanned
      lastElem <- letSubExp "lastElem" $ BasicOp $ BinOp (Sub Int64 OverflowUndef) n (Constant int64One)
      n' <- letSubExp "new_length" $ BasicOp $ Index flags_scanned (fullSlice (Prim int64) [DimFix lastElem])
    
      -- new_inds = map (\(flag, flag_scan) -> if flag == 1 then flag_scan - 1 else -1)
      flag <- newParam "flag" $ Prim int64
      flag_scan <- newParam "flag_scan" $ Prim int64
      new_inds_body <- runBodyBuilder . localScope (scopeOfLParams [flag, flag_scan]) $
        
        eBody
        [ eIf -- if flag == 1
          (eCmpOp (CmpEq int64) (eParam flag) (eSubExp (Constant int64One)))
          (eBody [eBinOp (Sub Int64 OverflowUndef) (eSubExp $ Var $ paramName flag_scan) (eSubExp $ Constant int64One)])
          (eBody [eSubExp $ Constant int64Neg])
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
      -- TODO: Need to loop over several bits
      -- bits = map (\bin -> (bin >> digit_n) & 1) new_bins
      bin <- newParam "bin" $ Prim int64
      digit_n <- letSubExp "zero_digit" $ zeroExp $ Prim int64 -- placeholder
      bits_map_bdy <- runBodyBuilder . localScope (scopeOfLParams [bin]) $
        eBody
        [
          eBinOp (And Int64)
            (eBinOp (LShr Int64) (eParam bin) (toExp digit_n))
            (eSubExp $ Constant $ IntValue $ intValue Int64 1)
        ]
      let bits_map_lam = Lambda [bin] bits_map_bdy [Prim int64]
      bits <- letExp "bits" $ Op $ Screma n' [new_bins] (ScremaForm [] [] bits_map_lam)

      -- Sort indexes based on bits (flag array)
      scatter_soac <- partition2Maker n' bits new_indexes 
      scatter_is <- letExp (baseString new_indexes ++ "_scattered") $ Op $ scatter_soac


      -- Collect sorted values
      -- new_vals = map(\i -> vs[i]) scatter_is
      val_idx <- newParam "val_idx" $ Prim int64
      new_vals_body <- runBodyBuilder . localScope (scopeOfLParams [val_idx]) $ do
        body <- letSubExp "body" $ BasicOp $ Index vs (fullSlice (Prim int64) [DimFix (Var (paramName val_idx))])     
        resultBodyM [body]
      let new_vals_lambda = Lambda [val_idx] new_vals_body [Prim int64]
      new_vals <- letExp "new_vals" $ Op $ Screma n' [new_indexes] $ ScremaForm [][] new_vals_lambda

      let true  = Constant $ IntValue $ intValue Int8 1
      let false = Constant $ IntValue $ intValue Int8 0

      -- Make flag array
      iota_n' <- letExp "iota_n'" $ BasicOp $ Iota n' (intConst Int64 0) (intConst Int64 1) Int64
      bin <- newParam "bin" $ Prim int64
      index <- newParam "iot_n'" $ Prim $ int64
      mk_flag_body <- runBodyBuilder . localScope (scopeOfLParams [bin, index]) $ do
        
        idx_minus_one <- letSubExp "idx_minus_one" $ BasicOp $ BinOp (Sub Int64 OverflowUndef) (Var $ paramName index) (intConst Int64 1)
        prev_elem <- letExp "prev_elem" $ BasicOp $ Index vs (fullSlice (Prim int64) [DimFix idx_minus_one]) 
        
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
              (resultBodyM $ [true])
              (eBody
                [
                  eIf
                    elemEq
                    (resultBodyM $ [false])
                    (resultBodyM $ [true])
                ])
          ]
      let mk_flag_lambda = Lambda [bin, index] mk_flag_body [Prim $ IntType Int8]
      final_flags <- letExp "final_flags" $ Op $ Screma n' [new_bins, scatter_is] $ ScremaForm [][] mk_flag_lambda


      -- Forward segmented exlusive scan in one array, reverse segmented exlusive scan in another.
      seg_scan_exc <- mkSegScanExc f ne n' new_vals final_flags
      fwd_scan <- letTupExp "fwd_scan" $ Op seg_scan_exc
      let [_, res] = fwd_scan
     
      -- Garbage to make the program compile
      let zeroSubExp = Constant $ int64Zero
      addStm $ Let pat aux $ BasicOp $ Index res $ fullSlice (Prim int64) [DimSlice zeroSubExp histDim (constant (1 :: Int64))]
      m
      
      insAdj orig_dst res


diffHist _ _ _ soac _ =
  error $ "Unsuported histogram: " ++ pretty soac
