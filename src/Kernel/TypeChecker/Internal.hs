{-|
Module      : Kernel.TypeChecker.Internal
Description : Type checker
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Implementation of type checker
-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Kernel.TypeChecker.Internal where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe

import Data.List (nub,find,genericIndex,genericLength,genericTake,genericDrop,genericSplitAt)
import Lens.Simple (makeLenses, over, view, use, (.=), (%=), (<~))

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Maybe as Maybe

import Debug.Trace

import Kernel.Name
import qualified Kernel.Level as Level
import Kernel.Level (Level)
import Kernel.Expr
import Kernel.Env
import Kernel.DefEqCache

{- TCMethods -}

data TypeError = UndefGlobalUniv Name
               | UndefLevelParam Name
               | TypeExpected Expr
               | FunctionExpected Expr
               | TypeMismatchAtApp Expr Expr
               | TypeMismatchAtDef Expr Expr
               | DeclHasFreeVars Expr
               | DeclHasLocals Expr
               | NameAlreadyDeclared Decl
               | DuplicateLevelParamName
               | ConstNotFound Name
               | ConstHasWrongNumLevels Name [Name] [Level]
               deriving (Eq,Show)

data TypeCheckerR = TypeCheckerR {
  tcrEnv :: Env ,
  tcrLPNames :: [Name]
}

data TypeCheckerS = TypeCheckerS {
  _tcsNextId :: Integer ,
  _tcsDefEqCache :: DefEqCache,
  _tcsInferTypeCache :: Map Expr Expr
  }

makeLenses ''TypeCheckerS

mkTypeCheckerR :: Env -> [Name] -> TypeCheckerR
mkTypeCheckerR env levelParamNames  = TypeCheckerR env levelParamNames

mkTypeCheckerS :: Integer -> TypeCheckerS
mkTypeCheckerS nextId = TypeCheckerS nextId mkDefEqCache Map.empty

type TCMethod = ExceptT TypeError (StateT TypeCheckerS (Reader TypeCheckerR))

tcEval :: Env -> [Name] -> Integer -> TCMethod a -> Either TypeError (a, Integer)
tcEval env lpNames nextId tcFn =
  let (x, tc) = runReader (runStateT (runExceptT tcFn) (mkTypeCheckerS nextId)) (mkTypeCheckerR env lpNames) in
  (,tcsNextId tc) <$> x

tcRun :: Env -> [Name] -> Integer -> TCMethod a -> Either TypeError a
tcRun env lpNames nextId = fmap fst . (tcEval env lpNames nextId)

check :: Env -> Decl -> Either TypeError ()
check env d = tcRun env (declLPNames d) 0 (checkMain d)

checkMain :: Decl -> TCMethod ()
checkMain d = do
  checkNoLocal (declType d)
  maybe (return ()) checkNoLocal (declVal d)
  checkName (declName d)
  checkDuplicatedParams
  sort <- inferType (declType d)
  ensureSort sort
  maybe (return ()) (checkValMatchesType (declType d)) (declVal d)

tcAssert :: Bool -> TypeError -> TCMethod ()
tcAssert b err = if b then return () else throwE err

{- Checkers -}

checkNoLocal :: Expr -> TCMethod ()
checkNoLocal e = tcAssert (not $ exprHasLocal e) (DeclHasLocals e)

checkName :: Name -> TCMethod()
checkName name = do
  env <- asks tcrEnv
  maybe (return ()) (throwE . NameAlreadyDeclared) (envLookupDecl env name)

checkDuplicatedParams :: TCMethod ()
checkDuplicatedParams = do
  lpNames <- asks tcrLPNames
  tcAssert (lpNames == nub lpNames) DuplicateLevelParamName

checkValMatchesType :: Expr -> Expr -> TCMethod()
checkValMatchesType ty val = do
  valTy <- inferType val
  isDefEq valTy ty >>= flip tcAssert (TypeMismatchAtDef valTy ty)

checkClosed :: Expr -> TCMethod ()
checkClosed e = tcAssert (not $ hasFreeVars e) (DeclHasFreeVars e)

checkLevel :: Level -> TCMethod ()
checkLevel level = do
  tcr <- ask
  maybe (return ()) (throwE . UndefLevelParam) (Level.getUndefParam level (tcrLPNames tcr))
  maybe (return ()) (throwE . UndefGlobalUniv) (Level.getUndefGlobal level (envGlobalNames $ tcrEnv tcr))

ensureSort :: Expr -> TCMethod SortData
ensureSort e = case e of
  Sort sort -> return sort
  _ -> do
    eWhnf <- whnf e
    case eWhnf of
      Sort sort -> return sort
      _ -> throwE $ TypeExpected eWhnf

ensureType :: Expr -> TCMethod SortData
ensureType e = inferType e >>= ensureSort

ensurePi :: Expr -> TCMethod BindingData
ensurePi e = case e of
  Pi pi -> return pi
  _ -> do
    eWhnf <- whnf e
    case eWhnf of
      Pi pi -> return pi
      _ -> throwE $ FunctionExpected eWhnf

{- Infer type -}

inferType :: Expr -> TCMethod Expr
inferType e = do
  checkClosed e
  inferTypeCache <- use tcsInferTypeCache
  case Map.lookup e inferTypeCache of
    Just ty -> return ty
    Nothing -> do
      ty <- case e of
        Local local -> return $ localType local
        Sort sort -> checkLevel (sortLevel sort) >> (return . mkSort . Level.mkSucc . sortLevel) sort
        Constant constant -> inferConstant constant
        Lambda lambda -> inferLambda lambda
        Pi pi -> inferPi pi
        App app -> inferApp app
      inferTypeCache %= Map.insert e ty
      return ty

inferConstant :: ConstantData -> TCMethod Expr
inferConstant c = do
  env <- asks tcrEnv
  case envLookupDecl env (constName c) of
    Nothing -> throwE (ConstNotFound c)
    Just d -> do
      let (dLPNames, cLevels) = (declLPNames d, constLevels c)
      tcAssert (length dLPNames == length cLevels) $ ConstHasWrongNumLevels (constName c) dLPNames cLevels
      mapM_ checkLevel cLevels
      return $ instantiateLevelParams (declType d) dLPNames cLevels

mkLocalFor :: BindingData -> TCMethod LocalData
mkLocalFor bind = do
  nextId <- gensym
  return $ mkLocalData (mkSystemNameI nextId) (bindingName bind) (bindingDomain bind) (bindingInfo bind)

inferLambda :: BindingData -> TCMethod Expr
inferLambda lam = do
  domainTy <- inferType (bindingDomain lam)
  ensureSort domainTy
  local <- mkLocalFor lam
  bodyTy <- inferType (instantiate (bindingBody lam) (Local local))
  return $ abstractPi local bodyTy

inferPi :: BindingData -> TCMethod Expr
inferPi pi = do
  domainTy <- inferType (bindingDomain pi)
  domainTyAsSort <- ensureSort domainTy
  local <- mkLocalFor pi
  bodyTy <- inferType (instantiate (bindingBody pi) (Local local))
  bodyTyAsSort <- ensureSort bodyTy
  return $ mkSort (Level.mkIMax (sortLevel domainTyAsSort) (sortLevel bodyTyAsSort))

inferApp :: AppData -> TCMethod Expr
inferApp app = do
  fnTy <- inferType (appFn app)
  fnTyAsPi <- ensurePi fnTy
  argTy <- inferType (appArg app)
  isEq <- isDefEq (bindingDomain fnTyAsPi) argTy
  if isEq then return $ instantiate (bindingBody fnTyAsPi) (appArg app)
    else throwE $ TypeMismatchAtApp (bindingDomain fnTyAsPi) argTy

{- Weak-head normal form (whnf) -}

whnf :: Expr -> TCMethod Expr
whnf e = do
  e1 <- whnfCoreDelta 0 e
  e2Maybe <- normalizeExt e1
  case e2Maybe of
    Nothing -> return e1
    Just e2 -> whnf e2

whnfCoreDelta :: Integer -> Expr -> TCMethod Expr
whnfCoreDelta w e = do
  e1 <- whnfCore e
  e2 <- unfoldNames w e1
  if e == e2 then return e else whnfCoreDelta w e2

whnfCore :: Expr -> TCMethod Expr
whnfCore e = case e of
  App app -> do
    let (fn, arg) = (appFn app, appArg app)
    fnWhnf <- whnfCore fn
    case fnWhnf of
      Lambda lam -> whnfCore (instantiate (bindingBody lam) arg)
      otherwise -> if fnWhnf == fn then return e else whnfCore (mkApp fnWhnf arg)
  _ -> return e

unfoldNames :: Integer -> Expr -> TCMethod Expr
unfoldNames w e = case e of
  App app -> let (op, args) = getAppOpArgs e in
              flip mkAppSeq args <$> unfoldNameCore w op
  _ -> unfoldNameCore w e

unfoldNameCore :: Integer -> Expr -> TCMethod Expr
unfoldNameCore w e = case e of
  Constant const -> do
    env <- asks tcrEnv
    maybe (return e)
      (\d -> case declVal d of
          Just dVal
            | declWeight d >= w && length (constLevels const) == length (declLPNames d)
              -> unfoldNameCore w (instantiateLevelParams dVal (declLPNames d) $ constLevels const)
          _ -> return e)
      (envLookupDecl env (constName const))
  _ -> return e

-- TODO(dhs): check for bools and support HoTT
normalizeExt :: Expr -> TCMethod (Maybe Expr)
normalizeExt e = runMaybeT (inductiveNormExt e `mplus` quotientNormExt e)

gensym :: TCMethod Integer
gensym = n %%= (n, n + 1)

-- is_def_eq

isDefEq :: Expr -> Expr -> TCMethod Bool
isDefEq t s = do
  success <- runExceptT (isDefEqMain t s)
  case success of
    Left answer -> return answer
    Right () -> return False

-- | If 'def_eq' short-circuits, then 'deqCommitTo deqFn' short-circuits with the same value, otherwise it shortcircuits with False.
deqCommitTo :: DefEqMethod () -> DefEqMethod ()
deqCommitTo deqFn = deqFn >> throwE False

-- | 'deqTryAnd' proceeds through its arguments, and short-circuits with True if all arguments short-circuit with True, otherwise it does nothing.
deqTryAnd :: [DefEqMethod ()] -> DefEqMethod ()
deqTryAnd [] = throwE True
deqTryAnd (defFn:defFns) = do
  success <- lift $ runExceptT deqFn
  case success of
    Left True -> deqTryAnd defFns
    _ -> return ()

-- | 'deqTryOr' proceeds through its arguments, and short-circuits with True if any of its arguments short-circuit with True, otherwise it does nothing.
deqTryOr :: [DefEqMethod ()] -> DefEqMethod ()
deqTryOr [] = return ()
deqTryOr (def_eq:def_eqs) = do
  success <- lift $ runExceptT def_eq
  case success of
    Left True -> throwE True
    _ -> deqTryOr def_eqs

-- This exception means we know if they are equal or not
type DefEqMethod = ExceptT Bool TCMethod

deqAssert b err = lift $ tcAssert b err

-- | 'deqTryIf b check' tries 'check' only if 'b' is true, otherwise does nothing.
deqTryIf :: Bool -> DefEqMethod () -> DefEqMethod ()
deqTryIf b check = if b then check else return ()

-- | Wrapper to add successes to the cache
isDefEqMain :: Expr -> Expr -> DefEqMethod ()
isDefEqMain t s = do
  success <- lift $ runExceptT (isDefEqCore t s)
  case success of
    Left True -> deqCacheAddEquiv t s >> throwE True
    Left False -> throwE False
    Right () -> return ()

isDefEqCore :: Expr -> Expr -> DefEqMethod ()
isDefEqCore t s = do
  quickIsDefEq t s
  tWhnf <- lift $ whnfCore t
  sWhnf <- lift $ whnfCore s
  deqTryIf (tWnhf /= t || sWhnf /= s) $ quickIsDefEq tWhnf sWhnf
  (tReduce,sReduce) <- reduceDefEq tWhnf sWhnf

  case (tReduce,sReduce) of
    (Constant const1, Constant const2) | constName const1 == constName const2 &&
                                         isDefEqLevels (constLevels const1) (constLevels const2) -> throwE True
    (Local local1, Local local2) | localName local1 == localName local2 ->
      throwE True
    (App app1,App app2) -> deqCommitTo (isDefEqApp tReduce sReduce)
    _ -> return ()

  isDefEqEta tReduce sReduce
  asks tcrEnv >>= (\env -> deqTryIf (isPropProofIrrel env) $ isDefEqProofIrrel tReduce sReduce)


reduceDefEq :: Expr -> Expr -> DefEqMethod (Expr, Expr)
reduceDefEq t s = do
  (t, s, status) <- lazyDeltaReduction t s >>= uncurry extReductionStep
  case status of
    DefUnknown -> return (t, s)
    Continue -> reduceDefEq t s

extReductionStep :: Expr -> Expr -> DefEqMethod (Expr, Expr, ReductionStatus)
extReductionStep t s = do
  tMaybe <- lift $ normalizeExt t
  sMaybe <- lift $ normalizeExt s

  (t_nn, s_nn, status) <- case (tMaybe, sMaybe) of
    (Nothing, Nothing) -> return (t_n, s_n, DefUnknown)
    (Just t_n, Nothing) -> do t_nn <- lift $ whnf_core t_n
                             return (t_nn, s_n, Continue)
    (Nothing, Just s_n) -> do s_nn <- lift $ whnf_core s_n
                             return (t_n, s_nn, Continue)
    (Just t_n, Just s_n) -> do t_nn <- lift $ whnf_core t_n
                              s_nn <- lift $ whnf_core s_n
                              return (t_nn, s_nn, Continue)

  case status of
    DefUnknown -> return (t, s, DefUnknown)
    Continue -> quickIsDefEq t s >> return (t, s, Continue)

lazyDeltaReduction :: Expr -> Expr -> DefEqMethod (Expr,Expr)
lazyDeltaReduction t s = do
  (t_n, s_n, status) <- lazyDeltaReductionStep t s
  case status of
    DefUnknown -> return (t_n, s_n)
    Continue -> lazyDeltaReduction t_n s_n

data ReductionStatus = Continue | DefUnknown
appendToPair :: (a, b) -> c -> (a, b, c)
appendToPair (x, y) z = (x, y, z)

isDelta :: Environment -> Expr -> Maybe Declaration
isDelta env e = envLookupDecl env (constName . getOperation $ e) >>= guard isDefinition

-- | Perform one lazy delta-reduction step.
lazyDeltaReductionStep :: Expr -> Expr -> DefEqMethod (Expr, Expr, ReductionStatus)
lazyDeltaReductionStep t s = do
  env <- asks tcrEnv
  (t_n, s_n, status) <-
    case (isDelta env t, isDelta env s) of
      (Nothing, Nothing) -> return (t, s, DefUnknown)
      (Just d_t, Nothing) -> (, s, Continue) <$> lift (unfoldNames 0 t >>= whnf_core)
      (Nothing, Just d_s) -> (t, , Continue) <$> lift (unfoldNames 0 s >>= whnf_core)
      (Just d_t, Just d_s) -> flip append_to_pair Continue <$> lazyDeltaReductionStepHelper d_t d_s t s
  case status of
    DefUnknown -> return (t_n, s_n, DefUnknown)
    Continue -> quickIsDefEq t_n s_n >> return (t_n,s_n,Continue)

lazyDeltaReductionStepHelper :: Declaration -> Declaration -> Expr -> Expr -> DefEqMethod (Expr,Expr)
lazyDeltaReductionStepHelper d_t d_s t s = do
  tc <- get
  case compare (declWeight d_t) (declWeight d_s) of
    LT -> (t, ) <$> lift (unfoldNames (declWeight d_t + 1) s >>= whnf_core)
    GT -> (, s) <$> lift (unfoldNames (declWeight d_s + 1) t >>= whnf_core)
    EQ ->
      case (t,s) of
        (App t_app, App s_app) -> do
          {- Optimization: we try to check if their arguments are definitionally equal.
             If they are, then t_n and s_n must be definitionally equal,
             and we can skip the delta-reduction step. -}
          isDefEqApp t s
          reduceBoth
        _ -> reduceBoth
      where
        reduceBoth = do
          t_dn <- lift $ unfoldNames (declWeight d_s - 1) t >>= whnf_core
          s_dn <- lift $ unfoldNames (declWeight d_t - 1) s >>= whnf_core
          return (t_dn, s_dn)

{- | Throw true if 't' and 's' are definitionally equal because they are applications of the form
    '(f a_1 ... a_n)' and '(g b_1 ... b_n)', where 'f' and 'g' are definitionally equal, and
    'a_i' and 'b_i' are also definitionally equal for every 1 <= i <= n.
    Throw 'False' otherwise.
-}
isDefEqApp :: Expr -> Expr -> DefEqMethod ()
isDefEqApp t s =
  deqTryAnd [isDefEqMain (getOperator t) (getOperator s),
               throwE (genericLength (getAppArgs t) == genericLength (getAppArgs s)),
               mapM_ (uncurry isDefEqMain) (zip (getAppArgs t) (getAppArgs s))]

isDefEqEta :: Expr -> Expr -> DefEqMethod ()
isDefEqEta t s = deqTryOr [isDefEqEtaCore t s, isDefEqEtaCore s t]

-- | Try to solve (fun (x : A), B) =?= s by trying eta-expansion on s
-- The 'by' indicates that it short-circuits False 't' and 's' are not equal by eta-expansion, even though they may be equal for another reason. The enclosing 'deq_any_of' ignores any 'False's.
isDefEqEtaCore :: Expr -> Expr -> DefEqMethod ()
isDefEqEtaCore t s = go t s where
  go (Lambda lam1) (Lambda lam2) = throwE False
  go (Lambda lam1) s = do
    s_ty_n <- lift $ infer_type s >>= whnf
    case s_ty_n of
      Pi pi -> let new_s = mkLambda (bindingName pi) (bindingDomain pi) (mkApp s (mkVar 0)) (bindingInfo pi) in
                deqCommitTo (isDefEqMain t new_s)
      _ -> throwE False
  go _ _ = throwE False

isProp :: Expr -> TCMethod Bool
isProp e = do
  e_ty <- inferType e
  e_ty_whnf <- whnf e_ty
  if e_ty_whnf == mkProp then return True else return False

isDefEqProofIrrel :: Expr -> Expr -> DefEqMethod ()
isDefEqProofIrrel t s = do
  t_ty <- lift $ inferType t
  s_ty <- lift $ inferType s
  t_ty_is_prop <- lift $ isProp t_ty
  deqTryIf t_ty_is_prop $ isDefEqMain t_ty s_ty

quickIsDefEq :: Expr -> Expr -> DefEqMethod ()
quickIsDefEq t s = do
  deqCacheIsEquiv t s
  case (t, s) of
    (Lambda lam1, Lambda lam2) -> deqCommitTo (isDefEqBinding lam1 lam2)
    (Pi pi1, Pi pi2) -> deqCommitTo (isDefEqBinding pi1 pi2)
    (Sort sort1, Sort sort2) -> throwE (sort_level sort1 == sort_level sort2)
    _ -> return ()

-- | Given lambda/Pi expressions 't' and 's', return true iff 't' is def eq to 's', which holds iff 'domain(t)' is definitionally equal to 'domain(s)' and 'body(t)' is definitionally equal to 'body(s)'
isDefEqBinding :: BindingData -> BindingData -> DefEqMethod ()
isDefEqBinding bind1 bind2 = do
  deqTryAnd  [(isDefEqMain (binding_domain bind1) (binding_domain bind2)),
                do nextId <- lift gensym
                   local <- return $ mkLocal (mkSystemNameI nextId) (bindingName bind1) (bindingDomain bind1) (bindingInfo bind1)
                   isDefEqMain (instantiate (bindingBody bind1) local) (instantiate (bindingBody bind2) local)]

isDefEqLevels :: [Level] -> [Level] -> Bool
isDefEqLevels ls1 ls2 = ls1 == ls2

deqCacheAddEquiv :: Expr -> Expr -> DefEqMethod ()
deqCacheAddEquiv e1 e2 = do
  eqv <- gets tcs_equiv_manager
  modify (\tc -> tc { tcs_equiv_manager = EM.add_equiv e1 e2 eqv })

deqCacheIsEquiv :: Expr -> Expr -> DefEqMethod ()
deqCacheIsEquiv e1 e2 = do
  deqCache <- use tcsDeqCache
  let (isEquiv, newDeqCache) = DeqCache.isEquiv e1 e2 deqCache
  tcsDeqCache .= newDeqCache
  if isEquiv then throwE True else return ()

{- extensions -}

liftMaybe :: (MonadPlus m) => Maybe a -> m a
liftMaybe = maybe mzero return

-- | Reduce terms 'e' of the form 'elim_k A C e p[A,b] (intro_k_i A b u)'
inductiveNormExt :: Expr -> MaybeT TCMethod Expr
inductiveNormExt e = do
  elimInfos <- use (envInductiveExt . indExtElimInfos)
  elimOpConst <- liftMaybe . maybeConstant . getOperator $ e
  einfo@(ExtElimInfo ind_name lp_names num_params num_ACe num_indices k_target dep_elim) <-
    liftMaybe $ Map.lookup (const_name elim_fn_const) elim_infos
  guard $ genericLength (get_app_args e) >= num_ACe + num_indices + 1
  let major_idx = num_ACe + num_indices
      major = genericIndex (get_app_args e) major_idx in do
    (intro_app,comp_rule) <- find_comp_rule einfo elim_fn_const major
    let elim_args = get_app_args e
        intro_args = get_app_args intro_app in do
      guard $ genericLength intro_args == num_params + (cr_num_rec_nonrec_args comp_rule)
      guard $ genericLength (const_levels elim_fn_const) == genericLength lp_names
      let rhs_args = reverse ((genericTake num_ACe elim_args) ++
                              (genericTake (cr_num_rec_nonrec_args comp_rule) $ genericDrop num_params intro_args))
          rhs_body = instantiate_univ_params (body_of_lambda $ cr_comp_rhs comp_rule) lp_names (const_levels elim_fn_const)
          rhs_body_instantiated = instantiate_seq rhs_body rhs_args
          extra_args = genericDrop (major_idx + 1) elim_args in do
        return $ mk_app_seq rhs_body_instantiated extra_args
  where
    find_comp_rule :: ExtElimInfo -> ConstantData -> Expr -> MaybeT TCMethod (Expr,CompRule)
    find_comp_rule einfo elim_fn_const major
      | eei_K_target einfo = do
        mb_result <- lift . runMaybeT $
                     (do intro_app <- to_intro_when_K einfo major
                         map_comp_rules <- liftM (iext_comp_rules . env_ind_ext . tcr_env) ask
                         intro_app_op_const <- liftMaybe $ maybe_constant (getOperator intro_app)
                         comp_rule <- liftMaybe $ Map.lookup (const_name intro_app_op_const) map_comp_rules
                         return (intro_app,comp_rule))
        case mb_result of
          Nothing -> regular_comp_rule einfo elim_fn_const major
          Just result -> return result
      | otherwise = regular_comp_rule einfo elim_fn_const major
    regular_comp_rule :: ExtElimInfo -> ConstantData -> Expr -> MaybeT TCMethod (Expr,CompRule)
    regular_comp_rule einfo elim_fn_const major = do
      intro_app <- lift $ whnf major
      comp_rule <- is_intro_for (const_name elim_fn_const) intro_app
      return (intro_app,comp_rule)


-- | Return 'True' if 'e' is an introduction rule for an eliminator named 'elim'
is_intro_for :: Name -> Expr -> MaybeT TCMethod CompRule
is_intro_for elim_name e = do
  map_comp_rules <- liftM (iext_comp_rules . env_ind_ext . tcr_env) ask
  intro_fn_const <- liftMaybe $ maybe_constant (getOperator e)
  comp_rule <- liftMaybe $ Map.lookup (const_name intro_fn_const) map_comp_rules
  guard (cr_elim_name comp_rule == elim_name)
  return comp_rule

-- | For datatypes that support K-axiom, given e an element of that type, we convert (if possible)
-- to the default constructor. For example, if (e : a = a), then this method returns (eq.refl a)
to_intro_when_K :: ExtElimInfo -> Expr -> MaybeT TCMethod Expr
to_intro_when_K einfo e = do
  env <- asks tcr_env
  assert (eei_K_target einfo) "to_intro_when_K should only be called when K_target holds" (return ())
  app_type <- lift $ infer_type e >>= whnf
  app_type_I <- return $ getOperator app_type
  app_type_I_const <- liftMaybe $ maybe_constant app_type_I
  guard (const_name app_type_I_const == eei_inductive_name einfo)
  new_intro_app <- liftMaybe $ mk_nullary_intro env app_type (eei_num_params einfo)
  new_type <- lift $ infer_type new_intro_app
  types_eq <- lift $ isDefEq app_type new_type
  guard types_eq
  return new_intro_app

-- | If 'op_name' is the name of a non-empty inductive datatype, then return the
--   name of the first introduction rule. Return 'Nothing' otherwise.
get_first_intro :: Environment -> Name -> Maybe Name
get_first_intro env op_name = do
  mutual_idecls <- Map.lookup op_name (iext_ind_infos $ env_ind_ext env)
  InductiveDecl _ _ intro_rules <- find (\(InductiveDecl ind_name _ _) -> ind_name == op_name) (mid_idecls mutual_idecls)
  IntroRule ir_name _ <- find (\_ -> True) intro_rules
  return ir_name

mk_nullary_intro :: Environment -> Expr -> Integer -> Maybe Expr
mk_nullary_intro env app_type num_params =
  let (op,args) = get_app_op_args app_type in do
    op_const <- maybe_constant op
    intro_name <- get_first_intro env (const_name op_const)
    return $ mk_app_seq (mk_constant intro_name (const_levels op_const)) (genericTake num_params args)

{- Quotient -}

quotient_norm_ext :: Expr -> MaybeT TCMethod Expr
quotient_norm_ext e = do
  env <- asks tcr_env
  guard (env_quot_enabled env)
  fn <- liftMaybe $ maybe_constant (getOperator e)
  (mk_pos,arg_pos) <- if const_name fn == quot_lift then return (5,3) else
                        if const_name fn == quot_ind then return (4,3) else
                          fail "no quot comp rule applies"
  args <- return $ get_app_args e
  guard $ genericLength args > mk_pos
  mk <- lift $ whnf (genericIndex args mk_pos)
  case mk of
    App mk_as_app -> do
      mk_fn <- return $ getOperator mk
      mk_fn_const <- liftMaybe $ maybe_constant mk_fn
      guard $ const_name mk_fn_const == quot_mk
      let f = genericIndex args arg_pos
          elim_arity = mk_pos + 1
          extra_args = genericDrop elim_arity args in
        return $ mk_app_seq (mk_app f (app_arg mk_as_app)) extra_args
    _ -> fail "element of type 'quot' not constructed with 'quot.mk'"
    where
      quot_lift = mk_name ["lift","quot"]
      quot_ind = mk_name ["ind","quot"]
      quot_mk = mk_name ["mk","quot"]
