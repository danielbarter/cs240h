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
import Lens.Simple (makeLenses, over, view, use, (.=), (%=), (<~), (%%=))

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Maybe as Maybe

import Debug.Trace

import Kernel.Name
import qualified Kernel.Level as Level
import Kernel.Level (Level)
import Kernel.Expr
import Kernel.Env
import qualified Kernel.DeqCache as DeqCache
import Kernel.DeqCache (DeqCache, mkDeqCache)

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
  _tcrEnv :: Env ,
  _tcrLPNames :: [Name]
}

makeLenses ''TypeCheckerR

data TypeCheckerS = TypeCheckerS {
  _tcsNextId :: Int,
  _tcsDeqCache :: DeqCache,
  _tcsInferTypeCache :: Map Expr Expr
  }

makeLenses ''TypeCheckerS

mkTypeCheckerR :: Env -> [Name] -> TypeCheckerR
mkTypeCheckerR env levelParamNames  = TypeCheckerR env levelParamNames

mkTypeCheckerS :: Int -> TypeCheckerS
mkTypeCheckerS nextId = TypeCheckerS nextId mkDeqCache Map.empty

type TCMethod = ExceptT TypeError (StateT TypeCheckerS (Reader TypeCheckerR))

tcEval :: Env -> [Name] -> Int -> TCMethod a -> Either TypeError (a, Int)
tcEval env lpNames nextId tcFn =
  let (x, tc) = runReader (runStateT (runExceptT tcFn) (mkTypeCheckerS nextId)) (mkTypeCheckerR env lpNames) in
  (, view tcsNextId tc) <$> x

tcRun :: Env -> [Name] -> Int -> TCMethod a -> Either TypeError a
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
  env <- asks _tcrEnv
  maybe (return ()) (throwE . NameAlreadyDeclared) (envLookupDecl name env)

checkDuplicatedParams :: TCMethod ()
checkDuplicatedParams = do
  lpNames <- asks _tcrLPNames
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
  maybe (return ()) (throwE . UndefLevelParam) $ Level.getUndefParam level (view tcrLPNames tcr)
  maybe (return ()) (throwE . UndefGlobalUniv) $ Level.getUndefGlobal level (view (tcrEnv . envGlobalNames) tcr)

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
      tcsInferTypeCache %= Map.insert e ty
      return ty

inferConstant :: ConstantData -> TCMethod Expr
inferConstant c = do
  env <- asks _tcrEnv
  case envLookupDecl (constName c) env of
    Nothing -> throwE . ConstNotFound . constName $ c
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

whnfCoreDelta :: Int -> Expr -> TCMethod Expr
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

unfoldNames :: Int -> Expr -> TCMethod Expr
unfoldNames w e = case e of
  App app -> let (op, args) = getAppOpArgs e in
              flip mkAppSeq args <$> unfoldNameCore w op
  _ -> unfoldNameCore w e

unfoldNameCore :: Int -> Expr -> TCMethod Expr
unfoldNameCore w e = case e of
  Constant const -> do
    env <- asks _tcrEnv
    maybe (return e)
      (\d -> case declVal d of
          Just dVal
            | declWeight d >= w && length (constLevels const) == length (declLPNames d)
              -> unfoldNameCore w (instantiateLevelParams dVal (declLPNames d) $ constLevels const)
          _ -> return e)
      (envLookupDecl (constName const) env)
  _ -> return e

-- TODO(dhs): check for bools and support HoTT
normalizeExt :: Expr -> TCMethod (Maybe Expr)
normalizeExt e = runMaybeT (inductiveNormExt e `mplus` quotientNormExt e)

gensym :: TCMethod Int
gensym = tcsNextId %%= \n -> (n, n + 1)

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
deqTryAnd (deqFn:deqFns) = do
  success <- lift $ runExceptT deqFn
  case success of
    Left True -> deqTryAnd deqFns
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
  t_n <- lift $ whnfCore t
  s_n <- lift $ whnfCore s
  deqTryIf (t_n /= t || s_n /= s) $ quickIsDefEq t_n s_n
  (t_nn, s_nn) <- reduceDefEq t_n s_n

  case (t_nn, t_nn) of
    (Constant const1, Constant const2) | constName const1 == constName const2 &&
                                         isDefEqLevels (constLevels const1) (constLevels const2) -> throwE True
    (Local local1, Local local2) | localName local1 == localName local2 ->
      throwE True
    (App app1,App app2) -> deqCommitTo (isDefEqApp t_nn s_nn)
    _ -> return ()

  isDefEqEta t_nn s_nn
  env <- asks _tcrEnv
  deqTryIf (isPropProofIrrel env) $ isDefEqProofIrrel t_nn s_nn


reduceDefEq :: Expr -> Expr -> DefEqMethod (Expr, Expr)
reduceDefEq t s = do
  (t, s, status) <- lazyDeltaReduction t s >>= uncurry extReductionStep
  case status of
    DefUnknown -> return (t, s)
    Continue -> reduceDefEq t s

extReductionStep :: Expr -> Expr -> DefEqMethod (Expr, Expr, ReductionStatus)
extReductionStep t s = do
  t_mb <- lift $ normalizeExt t
  s_mb <- lift $ normalizeExt s

  (t_nn, s_nn, status) <-
    case (t_mb, s_mb) of
     (Nothing, Nothing) -> return (t, s, DefUnknown)
     (Just t_n, Nothing) -> (, s, Continue) <$> (lift . whnfCore) t_n
     (Nothing, Just s_n) -> (t, , Continue) <$> (lift . whnfCore) s_n
     (Just t_n, Just s_n) -> do t_nn <- lift $ whnfCore t_n
                                s_nn <- lift $ whnfCore s_n
                                return (t_nn, s_nn, Continue)

  case status of
    DefUnknown -> return (t_nn, s_nn, DefUnknown)
    Continue -> quickIsDefEq t_nn s_nn >> return (t_nn, s_nn, Continue)

lazyDeltaReduction :: Expr -> Expr -> DefEqMethod (Expr,Expr)
lazyDeltaReduction t s = do
  (t_n, s_n, status) <- lazyDeltaReductionStep t s
  case status of
    DefUnknown -> return (t_n, s_n)
    Continue -> lazyDeltaReduction t_n s_n

data ReductionStatus = Continue | DefUnknown
appendToPair :: (a, b) -> c -> (a, b, c)
appendToPair (x, y) z = (x, y, z)

isDelta :: Env -> Expr -> Maybe Decl
isDelta env e = do
  const <- maybeConstant . getOperator $ e
  decl <- flip envLookupDecl env . constName $ const
  guard . isDefinition $ decl
  return decl

-- | Perform one lazy delta-reduction step.
lazyDeltaReductionStep :: Expr -> Expr -> DefEqMethod (Expr, Expr, ReductionStatus)
lazyDeltaReductionStep t s = do
  env <- asks _tcrEnv
  (t_n, s_n, status) <-
    case (isDelta env t, isDelta env s) of
      (Nothing, Nothing) -> return (t, s, DefUnknown)
      (Just d_t, Nothing) -> (, s, Continue) <$> lift (unfoldNames 0 t >>= whnfCore)
      (Nothing, Just d_s) -> (t, , Continue) <$> lift (unfoldNames 0 s >>= whnfCore)
      (Just d_t, Just d_s) -> flip appendToPair Continue <$> lazyDeltaReductionStepHelper d_t d_s t s
  case status of
    DefUnknown -> return (t_n, s_n, DefUnknown)
    Continue -> quickIsDefEq t_n s_n >> return (t_n,s_n,Continue)

lazyDeltaReductionStepHelper :: Decl -> Decl -> Expr -> Expr -> DefEqMethod (Expr,Expr)
lazyDeltaReductionStepHelper d_t d_s t s = do
  tc <- get
  case compare (declWeight d_t) (declWeight d_s) of
    LT -> (t, ) <$> lift (unfoldNames (declWeight d_t + 1) s >>= whnfCore)
    GT -> (, s) <$> lift (unfoldNames (declWeight d_s + 1) t >>= whnfCore)
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
          t_dn <- lift $ unfoldNames (declWeight d_s - 1) t >>= whnfCore
          s_dn <- lift $ unfoldNames (declWeight d_t - 1) s >>= whnfCore
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
    s_ty_n <- lift $ inferType s >>= whnf
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
    (Sort sort1, Sort sort2) -> throwE (sortLevel sort1 == sortLevel sort2)
    _ -> return ()

-- | Given lambda/Pi expressions 't' and 's', return true iff 't' is def eq to 's', which holds iff 'domain(t)' is definitionally equal to 'domain(s)' and 'body(t)' is definitionally equal to 'body(s)'
isDefEqBinding :: BindingData -> BindingData -> DefEqMethod ()
isDefEqBinding bind1 bind2 = do
  deqTryAnd  [(isDefEqMain (bindingDomain bind1) (bindingDomain bind2)),
                do nextId <- lift gensym
                   local <- return $ mkLocal (mkSystemNameI nextId) (bindingName bind1) (bindingDomain bind1) (bindingInfo bind1)
                   isDefEqMain (instantiate (bindingBody bind1) local) (instantiate (bindingBody bind2) local)]

isDefEqLevels :: [Level] -> [Level] -> Bool
isDefEqLevels ls1 ls2 = ls1 == ls2

deqCacheAddEquiv :: Expr -> Expr -> DefEqMethod ()
deqCacheAddEquiv e1 e2 = tcsDeqCache %= DeqCache.addEquiv e1 e2

deqCacheIsEquiv :: Expr -> Expr -> DefEqMethod ()
deqCacheIsEquiv e1 e2 = do
  deqCache <- use tcsDeqCache
  let (isEquiv, newDeqCache) = DeqCache.isEquiv e1 e2 deqCache
  tcsDeqCache .= newDeqCache
  if isEquiv then throwE True else return ()

{- extensions -}

liftMaybe :: (MonadPlus m) => Maybe a -> m a
liftMaybe = maybe mzero return

--inductiveNormExt :: Expr -> MaybeT TCMethod Expr
--inductiveNormExt e = undefined

--quotientNormExt :: Expr -> MaybeT TCMethod Expr
--quotientNormExt e = undefined

-- | Reduce terms 'e' of the form 'elim_k A C e p[A,b] (intro_k_i A b u)'
inductiveNormExt :: Expr -> MaybeT TCMethod Expr
inductiveNormExt e = do
  elimInfos <- use (envInductiveExt . indExtElimInfos)
  elimOpConst <- liftMaybe . maybeConstant . getOperator $ e
  einfo@(ExtElimInfo indName lpNames numParams numACe numIndices kTarget depElim) <-
    liftMaybe $ Map.lookup (constName elimOpConst) elimInfos
  guard $ genericLength (getAppArgs e) >= numACe + numIndices + 1
  let majorIdx = numACe + numIndices
      major = index (getAppArgs e) majorIdx in do
    (introApp,compRule) <- findCompRule einfo elimOpConst major
    let elimArgs = getAppArgs e
        introArgs = getAppArgs introApp in do
      guard $ length introArgs == numParams + (compRuleNumArgs compRule)
      guard $ length (constLevels elimOpConst) == length lpNames
      let rhsArgs = reverse ((take numACe elimArgs) ++
                              (take (compRuleNumArgs compRule) $ drop numParams introArgs))
          rhsBody = instantiateUnivParams (innerBodyOfLambda . compRuleRHS $ compRule) lpNames (constLevels elimOpConst)
          rhsBodyInstantiated = instantiateSeq rhsBody rhsArgs
          extraArgs = drop (majorIdx + 1) elimArgs in
       return $ mkAppSeq rhsBodyInstantiated extraArgs
  where
    findCompRule :: ExtElimInfo -> ConstantData -> Expr -> MaybeT TCMethod (Expr,CompRule)
    findCompRule einfo elimOpConst major
      | eei_kTarget einfo = do
        mb_result <- lift . runMaybeT $
                     (do introApp <- to_intro_when_K einfo major
                         map_compRules <- liftM (iext_compRules . env_ind_ext . tcr_env) ask
                         introApp_op_const <- liftMaybe $ maybe_constant (getOperator introApp)
                         compRule <- liftMaybe $ Map.lookup (constName introApp_op_const) map_compRules
                         return (introApp,compRule))
        case mb_result of
          Nothing -> regular_compRule einfo elimOpConst major
          Just result -> return result
      | otherwise = regular_compRule einfo elimOpConst major
    regular_compRule :: ExtElimInfo -> ConstantData -> Expr -> MaybeT TCMethod (Expr,CompRule)
    regular_compRule einfo elimOpConst major = do
      introApp <- lift $ whnf major
      compRule <- is_intro_for (constName elimOpConst) introApp
      return (introApp,compRule)


-- | Return 'True' if 'e' is an introduction rule for an eliminator named 'elim'
is_intro_for :: Name -> Expr -> MaybeT TCMethod CompRule
is_intro_for elim_name e = do
  map_compRules <- liftM (iext_compRules . env_ind_ext . tcr_env) ask
  intro_fn_const <- liftMaybe $ maybe_constant (getOperator e)
  compRule <- liftMaybe $ Map.lookup (constName intro_fn_const) map_compRules
  guard (cr_elim_name compRule == elim_name)
  return compRule

-- | For datatypes that support K-axiom, given e an element of that type, we convert (if possible)
-- to the default constructor. For example, if (e : a = a), then this method returns (eq.refl a)
to_intro_when_K :: ExtElimInfo -> Expr -> MaybeT TCMethod Expr
to_intro_when_K einfo e = do
  env <- asks tcr_env
  assert (eei_kTarget einfo) "to_intro_when_K should only be called when kTarget holds" (return ())
  app_type <- lift $ inferType e >>= whnf
  app_type_I <- return $ getOperator app_type
  app_type_I_const <- liftMaybe $ maybe_constant app_type_I
  guard (constName app_type_I_const == eei_inductive_name einfo)
  new_introApp <- liftMaybe $ mk_nullary_intro env app_type (eei_numParams einfo)
  new_type <- lift $ inferType new_introApp
  types_eq <- lift $ isDefEq app_type new_type
  guard types_eq
  return new_introApp

-- | If 'op_name' is the name of a non-empty inductive datatype, then return the
--   name of the first introduction rule. Return 'Nothing' otherwise.
get_first_intro :: Env -> Name -> Maybe Name
get_first_intro env op_name = do
  mutual_idecls <- Map.lookup op_name (iext_ind_infos $ env_ind_ext env)
  InductiveDecl _ _ intro_rules <- find (\(InductiveDecl indName _ _) -> indName == op_name) (mid_idecls mutual_idecls)
  IntroRule ir_name _ <- find (\_ -> True) intro_rules
  return ir_name

mk_nullary_intro :: Env -> Expr -> Int -> Maybe Expr
mk_nullary_intro env app_type numParams =
  let (op,args) = get_app_op_args app_type in do
    op_const <- maybe_constant op
    intro_name <- get_first_intro env (constName op_const)
    return $ mk_app_seq (mk_constant intro_name (constLevels op_const)) (genericTake numParams args)

{-
{- Quotient -}

quotient_norm_ext :: Expr -> MaybeT TCMethod Expr
quotient_norm_ext e = do
  env <- asks tcr_env
  guard (env_quot_enabled env)
  fn <- liftMaybe $ maybe_constant (getOperator e)
  (mk_pos,arg_pos) <- if constName fn == quot_lift then return (5,3) else
                        if constName fn == quot_ind then return (4,3) else
                          fail "no quot comp rule applies"
  args <- return $ getAppArgs e
  guard $ genericLength args > mk_pos
  mk <- lift $ whnf (genericIndex args mk_pos)
  case mk of
    App mk_as_app -> do
      mk_fn <- return $ getOperator mk
      mk_fn_const <- liftMaybe $ maybe_constant mk_fn
      guard $ constName mk_fn_const == quot_mk
      let f = genericIndex args arg_pos
          elim_arity = mk_pos + 1
          extra_args = genericDrop elim_arity args in
        return $ mk_app_seq (mk_app f (app_arg mk_as_app)) extra_args
    _ -> fail "element of type 'quot' not constructed with 'quot.mk'"
    where
      quot_lift = mk_name ["lift","quot"]
      quot_ind = mk_name ["ind","quot"]
      quot_mk = mk_name ["mk","quot"]
-}
