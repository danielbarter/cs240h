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

import Data.List (nub, (!!), take, drop, splitAt, length)
import Lens.Simple (makeLenses, over, view, use, (.=), (%=), (<~), (%%=))

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Maybe as Maybe

import Debug.Trace

import Kernel.Name
import qualified Kernel.Level as Level
import Kernel.Level (Level)
import Kernel.Expr
import qualified Kernel.DeqCache as DeqCache
import Kernel.DeqCache (DeqCache, mkDeqCache)

import qualified Data.Maybe as Maybe

{- Inductive extension -}

data IntroRule = IntroRule Name Expr deriving (Show)

data IndDecl = IndDecl {
  _indDeclNumParams :: Integer,
  _indDeclLPNames :: [Name],
  _indDeclName :: Name,
  _indDeclType :: Expr,
  _indDeclIntroRules :: [IntroRule]
  } deriving (Show)

makeLenses ''IndDecl

data ElimInfo = ElimInfo {
  elimInfoIndName :: Name, -- ^ name of the inductive datatype associated with eliminator
  elimInfoLevelParamNames :: [Name], -- ^ level parameter names used in computational rule
  elimInfoNumParams :: Int, -- ^ number of global parameters A
  elimInfoNumACe :: Int, -- ^ sum of number of global parameters A, type formers C, and minor preimises e.
  elimInfoNumIndices :: Int, -- ^ number of inductive datatype indices
  -- | We support K-like reduction when the inductive datatype is in Type.{0} (aka Prop), proof irrelevance is enabled,
  -- it has only one introduction rule, the introduction rule has "0 arguments".
  elimInfoKTarget :: Bool,
  elimInfoDepElim :: Bool -- ^ elimInfoDepElim == true if dependent elimination is used for this eliminator
  } deriving (Show)

-- | Represents a single computation rule
data CompRule = CompRule {
  compRuleElimName :: Name, -- ^ name of the corresponding eliminator
  compRuleNumArgs :: Int, -- ^ sum of number of rec_args and nonrec_args in the corresponding introduction rule.
  compRuleRHS :: Expr -- ^ computational rule RHS: Fun (A, C, e, b, u), (e_k_i b u v)
  } deriving (Show)

data InductiveExt = InductiveExt {
  _indExtElimInfos :: Map Name ElimInfo,
  _indExtCompRules :: Map Name CompRule,
  _indExtIntroNameToIndName :: Map Name Name,
  _indExtIndDecls :: Map Name IndDecl
  } deriving (Show)

makeLenses ''InductiveExt

mkEmptyInductiveExt = InductiveExt Map.empty Map.empty Map.empty Map.empty

{- Environments -}

data Decl = Decl {
  declName :: Name,
  declLPNames :: [Name],
  declType :: Expr,
  declVal :: Maybe Expr,
  declWeight :: Int
  } deriving (Eq,Show)

data Env = Env {
  _envDecls :: Map Name Decl,
  _envGlobalNames :: Set Name,
  _envIndExt :: InductiveExt,
  _envQuotEnabled :: Bool,
  _envPropProofIrrel :: Bool,
  _envPropImpredicative :: Bool
  } deriving (Show)

makeLenses ''Env

mkStdEnv = Env Map.empty Set.empty mkEmptyInductiveExt True True True

{- Decls -}

mkDefinition :: Env -> Name -> [Name] -> Expr -> Expr -> Decl
mkDefinition env name levelParamNames ty val =
  Decl name levelParamNames ty (Just val) (1 + getMaxDeclWeight env val)

mkAxiom :: Name -> [Name] -> Expr -> Decl
mkAxiom name lpNames ty = Decl name lpNames ty Nothing 0

isDefinition :: Decl -> Bool
isDefinition decl = Maybe.isJust $ declVal decl

getMaxDeclWeight :: Env -> Expr -> Int
getMaxDeclWeight env e = case e of
  Var _ -> 0
  Local local -> getMaxDeclWeight env (localType local)
  Constant const -> maybe 0 declWeight (envLookupDecl (constName const) env)
  Sort _ -> 0
  Lambda lam -> getMaxDeclWeight env (bindingDomain lam) `max` getMaxDeclWeight env (bindingBody lam)
  Pi pi -> getMaxDeclWeight env (bindingDomain pi) `max` getMaxDeclWeight env (bindingBody pi)
  App app -> getMaxDeclWeight env (appFn app) `max` getMaxDeclWeight env (appArg app)


envLookupDecl :: Name -> Env -> Maybe Decl
envLookupDecl name  = Map.lookup name . view envDecls


envHasGlobalLevel :: Name -> Env -> Bool
envHasGlobalLevel name = Set.member name . view envGlobalNames

envAddGlobalLevel :: Name -> Env -> Env
envAddGlobalLevel name env = case envHasGlobalLevel name env of
                              False -> over envGlobalNames (Set.insert name) env


envAddIndDecl :: IndDecl -> Env -> Env
envAddIndDecl idecl = over (envIndExt . indExtIndDecls) $ Map.insert (view indDeclName idecl) idecl

envAddIntroRule :: Name -> Name -> Env -> Env
envAddIntroRule irName indName = over (envIndExt . indExtIntroNameToIndName) $ Map.insert irName indName

envAddElimInfo :: ElimInfo -> Env -> Env
envAddElimInfo elimInfo = over (envIndExt . indExtElimInfos) $ Map.insert (elimInfoIndName elimInfo) elimInfo

envAddCompRule :: Name -> CompRule -> Env -> Env
envAddCompRule irName compRule = over (envIndExt . indExtCompRules) $ Map.insert irName compRule


{- TCMethods -}

data TypeError = UndefGlobalLevel Name
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
  maybe (return ()) (throwE . UndefGlobalLevel) $ Level.getUndefGlobal level (view (tcrEnv . envGlobalNames) tcr)

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
  deqTryIf (view envPropProofIrrel env) $ isDefEqProofIrrel t_nn s_nn


reduceDefEq :: Expr -> Expr -> DefEqMethod (Expr, Expr)
reduceDefEq t s = do
  (t, s, status) <- lazyDeltaReduction t s >>= uncurry extReductionStep
  case status of
    DefUnknown -> return (t, s)
    Continue -> reduceDefEq t s

extReductionStep :: Expr -> Expr -> DefEqMethod (Expr, Expr, ReductionStatus)
extReductionStep t s = do
  mb_t <- lift $ normalizeExt t
  mb_s <- lift $ normalizeExt s

  (t_nn, s_nn, status) <-
    case (mb_t, mb_s) of
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
               throwE (length (getAppArgs t) == length (getAppArgs s)),
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
  elimInfos <- liftM (view $ tcrEnv . envIndExt . indExtElimInfos) $ ask
  elimOpConst <- liftMaybe . maybeConstant . getOperator $ e
  einfo@(ElimInfo indName lpNames numParams numACe numIndices kTarget depElim) <-
    liftMaybe $ Map.lookup (constName elimOpConst) elimInfos
  guard $ length (getAppArgs e) >= numACe + numIndices + 1
  let majorIdx = numACe + numIndices
  let major = (getAppArgs e) !! majorIdx
  (introApp,compRule) <- findCompRule einfo elimOpConst major
  let elimArgs = getAppArgs e
  let introArgs = getAppArgs introApp
  guard $ length introArgs == numParams + (compRuleNumArgs compRule)
  guard $ length (constLevels elimOpConst) == length lpNames
  let rhsArgs = reverse ((take numACe elimArgs) ++ (take (compRuleNumArgs compRule) $ drop numParams introArgs))
  let rhsBody = instantiateLevelParams (innerBodyOfLambda . compRuleRHS $ compRule) lpNames (constLevels elimOpConst)
  let rhsBodyInstantiated = instantiateSeq rhsBody rhsArgs
  let extraArgs = drop (majorIdx + 1) elimArgs
  return $ mkAppSeq rhsBodyInstantiated extraArgs
    where
      findCompRule :: ElimInfo -> ConstantData -> Expr -> MaybeT TCMethod (Expr, CompRule)
      findCompRule einfo elimOpConst major
        | elimInfoKTarget einfo = do
            mb_result <- lift . runMaybeT $
                         (do introApp <- toIntroWhenK einfo major
                             compRules <- liftM (view $ tcrEnv . envIndExt . indExtCompRules) ask
                             introAppOpConst <- liftMaybe . maybeConstant . getOperator $ introApp
                             compRule <- liftMaybe $ Map.lookup (constName introAppOpConst) compRules
                             return (introApp, compRule))
            case mb_result of
             Nothing -> regularCompRule einfo elimOpConst major
             Just result -> return result
        | otherwise = regularCompRule einfo elimOpConst major
      regularCompRule :: ElimInfo -> ConstantData -> Expr -> MaybeT TCMethod (Expr, CompRule)
      regularCompRule einfo elimOpConst major = do
        introApp <- lift $ whnf major
        compRule <- isIntroFor (constName elimOpConst) introApp
        return (introApp, compRule)

-- | Return 'True' if 'e' is an introduction rule for an eliminator named 'elim'
isIntroFor :: Name -> Expr -> MaybeT TCMethod CompRule
isIntroFor elimName e = do
  compRules <- liftM (view $ tcrEnv . envIndExt . indExtCompRules) ask
  introFnConst <- liftMaybe $ maybeConstant (getOperator e)
  compRule <- liftMaybe $ Map.lookup (constName introFnConst) compRules
  guard (compRuleElimName compRule == elimName)
  return compRule

-- | For datatypes that support K-axiom, given e an element of that type, we convert (if possible)
-- to the default constructor. For example, if (e : a = a), then this method returns (eq.refl a)
toIntroWhenK :: ElimInfo -> Expr -> MaybeT TCMethod Expr
toIntroWhenK einfo e = do
  env <- asks _tcrEnv
  appType <- lift $ inferType e >>= whnf
  let appTypeOp = getOperator appType
  appTypeOpConst <- liftMaybe $ maybeConstant appTypeOp
  guard (constName appTypeOpConst == elimInfoIndName einfo)
  newIntroApp <- liftMaybe $ mkNullaryIntro env appType (elimInfoNumParams einfo)
  newType <- lift $ inferType newIntroApp
  typesEq <- lift $ isDefEq appType newType
  guard typesEq
  return newIntroApp

-- | If 'op_name' is the name of a non-empty inductive datatype, then return the
--   name of the first introduction rule. Return 'Nothing' otherwise.
getFirstIntro :: Env -> Name -> Maybe Name
getFirstIntro env opName = do
  IndDecl _ _ _ _ [IntroRule irName _] <- Map.lookup opName $ view (envIndExt . indExtIndDecls) env
  return irName

mkNullaryIntro :: Env -> Expr -> Int -> Maybe Expr
mkNullaryIntro env appType numParams =
  let (op, args) = getAppOpArgs appType in do
    opConst <- maybeConstant op
    introName <- getFirstIntro env (constName opConst)
    return $ mkAppSeq (mkConstant introName (constLevels opConst)) (take numParams args)

{- Quotient -}

quotientNormExt :: Expr -> MaybeT TCMethod Expr
quotientNormExt e = do
  env <- asks _tcrEnv
  guard $ view envQuotEnabled env
  op <- liftMaybe $ maybeConstant (getOperator e)
  (mkPos, argPos) <- if constName op == quotLift then return (5,3) else
                       if constName op == quotInd then return (4,3) else
                         fail "no quot comp rule applies"
  args <- return $ getAppArgs e
  guard $ length args > mkPos
  mk <- lift . whnf $ args !! mkPos
  case mk of
    App mkAsApp -> do
      let mkOp = getOperator mk
      mkOpConst <- liftMaybe $ maybeConstant mkOp
      guard $ constName mkOpConst == quotMk
      let f = args !! argPos
      let elimArity = mkPos + 1
      let extraArgs = drop elimArity args
      return $ mkAppSeq (mkApp f (appArg mkAsApp)) extraArgs
    _ -> fail "element of type 'quot' not constructed with 'quot.mk'"
    where
      quotLift = mkName ["lift","quot"]
      quotInd = mkName ["ind","quot"]
      quotMk = mkName ["mk","quot"]

{- Adding to the environment -}

envAddDecl :: Decl -> Env -> Either TypeError Env
envAddDecl decl env =
  case check env decl of
    Left err -> Left err
    Right () -> case envLookupDecl (declName decl) env of
                 Nothing -> Right $ over envDecls (Map.insert (declName decl) decl) env

envAddAxiom :: Name -> [Name] -> Expr -> Env -> Either TypeError Env
envAddAxiom name lpNames ty = envAddDecl (mkAxiom name lpNames ty)

envAddDefinition :: Name -> [Name] -> Expr -> Expr -> Env -> Either TypeError Env
envAddDefinition name lpNames ty val env = envAddDecl (mkDefinition env name lpNames ty val) env
