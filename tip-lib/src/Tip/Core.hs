{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE ExplicitForAll, FlexibleContexts, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
-- | General functions for constructing and examining Tip syntax.
module Tip.Core(module Tip.Types, module Tip.Core) where

#include "errors.h"
import Tip.Types
import Tip.Fresh
import Tip.Utils
import Tip.Pretty
import Data.Traversable (Traversable)
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Generics.Geniplate
import Data.List ((\\),partition)
import Data.Ord
import Control.Monad
import qualified Data.Map as Map
import Control.Applicative ((<|>))

infix  4 ===
-- infixr 3 /\
infixr 2 \/
infixr 1 ==>
infixr 0 ===>

-- * Constructing expressions

(===) :: Expr a -> Expr a -> Expr a
e1 === e2 = Builtin Equal :@: [e1,e2]

(=/=) :: Expr a -> Expr a -> Expr a
e1 =/= e2 = Builtin Distinct :@: [e1,e2]

oppositeQuant :: Quant -> Quant
oppositeQuant Forall = Exists
oppositeQuant Exists = Forall

gentleNeg :: Expr a -> Expr a
gentleNeg (Builtin Not :@: [e]) = e
gentleNeg e = Builtin Not :@: [e]

neg :: Expr a -> Expr a
neg (Quant qi q lcs e)   = Quant qi (oppositeQuant q) lcs (neg e)
neg (Builtin And :@: es) = Builtin Or  :@: map neg es
neg (Builtin Or  :@: es) = Builtin And :@: map neg es
neg (Builtin Not :@: [e]) = e
neg (Builtin op :@: [e1,e2])
  | Equal    <- op = e1 =/= e2
  | Distinct <- op = e1 === e2
neg e
  | Just b <- boolView e = if b then falseExpr else trueExpr
  | otherwise = Builtin Not :@: [e]

(/\) :: Expr a -> Expr a -> Expr a
e1 /\ e2
  | Just b <- boolView e1 = if b then e2 else falseExpr
  | Just b <- boolView e2 = if b then e1 else falseExpr
  | otherwise = Builtin And :@: [e1,e2]

(\/) :: Expr a -> Expr a -> Expr a
e1 \/ e2
  | Just b <- boolView e1 = if b then trueExpr else e2
  | Just b <- boolView e2 = if b then trueExpr else e1
  | otherwise = Builtin Or :@: [e1,e2]

ands :: [Expr a] -> Expr a
ands xs =
  case flatAnd (foldl (/\) trueExpr xs) of
    []  -> trueExpr
    [x] -> x
    xs  -> Builtin And :@: xs
  where
    flatAnd (Builtin And :@: xs) = concatMap flatAnd xs
    flatAnd x = [x]

ors :: [Expr a] -> Expr a
ors xs =
  case flatOr (foldl (\/) falseExpr xs) of
    []  -> falseExpr
    [x] -> x
    xs  -> Builtin Or :@: xs
  where
    flatOr (Builtin Or :@: xs) = concatMap flatOr xs
    flatOr x = [x]

(==>) :: Expr a -> Expr a -> Expr a
e1 ==> e2
  | Just a <- boolView e1 = if a then e2 else trueExpr
  | Just b <- boolView e2 = if b then trueExpr else neg e1
  | otherwise = Builtin Implies :@: [e1,e2]

(===>) :: [Expr a] -> Expr a -> Expr a
xs ===> y = foldr (==>) y xs

mkQuant :: Quant -> [Local a] -> Expr a -> Expr a
mkQuant q [] e = e
mkQuant q xs e = Quant NoInfo q xs e

bool :: Bool -> Expr a
bool = literal . Bool

trueExpr :: Expr a
trueExpr  = bool True

falseExpr :: Expr a
falseExpr = bool False

makeIf :: Expr a -> Expr a -> Expr a -> Expr a
makeIf c t f
  | Just b <- boolView c = if b then t else f
  | otherwise = Match c [Case (LitPat (Bool True)) t,Case (LitPat (Bool False)) f]

intLit :: Integer -> Expr a
intLit = literal . Int

literal :: Lit -> Expr a
literal lit = Builtin (Lit lit) :@: []

intType :: Type a
intType = BuiltinType Integer

realType :: Type a
realType = BuiltinType Real

boolType :: Type a
boolType = BuiltinType Boolean

applyFunction :: Function a -> [Type a] -> [Expr a] -> Expr a
applyFunction fn@Function{..} tyargs args
  = Gbl (Global func_name (funcType fn) tyargs) :@: args

applySignature :: Signature a -> [Type a] -> [Expr a] -> Expr a
applySignature Signature{..} tyargs args
  = Gbl (Global sig_name sig_type tyargs) :@: args

apply :: Expr a -> [Expr a] -> Expr a
apply e es@(_:_) = Builtin At :@: (e:es)
apply _ [] = ERROR("tried to construct nullary lambda function")

applyTypeIn :: Ord a => ((Type a -> Type a) -> f a -> f a) -> [a] -> [Type a] -> f a -> f a
applyTypeIn transformer tvs tys
  | length tvs /= length tys = ERROR("wrong number of type arguments")
  | otherwise = transformer $ \ty -> case ty of TyVar x -> Map.findWithDefault ty x m
                                                _       -> ty
  where
    m = Map.fromList (zip tvs tys)

applyType :: Ord a => [a] -> [Type a] -> Type a -> Type a
applyType = applyTypeIn transformType

applyTypeInExpr :: Ord a => [a] -> [Type a] -> Expr a -> Expr a
applyTypeInExpr = applyTypeIn transformTypeInExpr

applyTypeInDecl :: Ord a => [a] -> [Type a] -> Decl a -> Decl a
applyTypeInDecl = applyTypeIn transformTypeInDecl

applyPolyType :: Ord a => PolyType a -> [Type a] -> ([Type a], Type a)
applyPolyType PolyType{..} tys =
  (map (applyType polytype_tvs tys) polytype_args,
   applyType polytype_tvs tys polytype_res)

gblType :: Ord a => Global a -> ([Type a], Type a)
gblType Global{..} = applyPolyType gbl_type gbl_args

makeLets :: [(Local a,Expr a)] -> Expr a -> Expr a
makeLets []           e = e
makeLets ((x,ex):xes) e = Let x ex (makeLets xes e)

-- * Predicates and examinations on expressions

collectLets :: Expr a -> ([(Local a,Expr a)],Expr a)
collectLets (Let y rhs e) = let (bs,e') = collectLets e in ((y,rhs):bs,e')
collectLets e             = ([],e)

litView :: Expr a -> Maybe Lit
litView (Builtin (Lit l) :@: []) = Just l
litView _ = Nothing

boolView :: Expr a -> Maybe Bool
boolView e = case litView e of Just (Bool b) -> Just b
                               _             -> Nothing

forallView :: Expr a -> ([Local a],Expr a)
forallView (Quant _ Forall vs1 e) = let (vs2,e') = forallView e
                                    in (vs1++vs2,e')
forallView e                      = ([],e)

-- | A representation of Nested patterns, used in 'patternMatchingView'
data DeepPattern a
  = DeepConPat (Global a) [DeepPattern a]
  | DeepVarPat (Local a)
  | DeepLitPat Lit

-- | Match as left-hand side pattern-matching definitions
--
-- Stops at default patterns, for simplicity
patternMatchingView :: Ord a => [Local a] -> Expr a -> [([DeepPattern a],Expr a)]
patternMatchingView = go . map DeepVarPat
  where
  go ps (Match (Lcl l) brs)
    | null [ () | Case Default _ <- brs ]
    , Just k <- modDeepPatterns l ps
    = concat [ go (k (deep p)) ((patToExpr p `unsafeSubst` l) rhs) | Case p rhs <- brs ]
  go ps e = [(ps,e)]

  (<$$>) :: (Functor f,Functor g) => (a -> b) -> f (g a) -> f (g b)
  (<$$>) = fmap . fmap

  -- Variable not in pattern: returns Nothing
  modDeepPattern :: Eq a => Local a -> DeepPattern a -> Maybe (DeepPattern a -> DeepPattern a)
  modDeepPattern l (DeepConPat g nps) = DeepConPat g <$$> modDeepPatterns l nps
  modDeepPattern l (DeepVarPat l') | l == l'   = Just id
                                   | otherwise = Nothing
  modDeepPattern l (DeepLitPat lit) = Nothing

  -- Variable not in patterns: returns Nothing
  modDeepPatterns :: Eq a => Local a -> [DeepPattern a] -> Maybe (DeepPattern a -> [DeepPattern a])
  modDeepPatterns l (np:nps) = ((:nps) <$$> modDeepPattern l np) <|> ((np:) <$$> modDeepPatterns l nps)
  modDeepPatterns l []       = Nothing

  deep :: Pattern a -> DeepPattern a
  deep (ConPat g ls) = DeepConPat g (map DeepVarPat ls)
  deep (LitPat lit)  = DeepLitPat lit
  deep Default       = error "patternMatchingView.deep: Default"

  patToExpr :: Pattern a -> Expr a
  patToExpr (ConPat g ls) = Gbl g :@: map Lcl ls
  patToExpr (LitPat lit)  = literal lit
  patToExpr Default       = error "patternMatchingView.patToExpr: Default"

ifView :: Expr a -> Maybe (Expr a,Expr a,Expr a)
ifView (Match c [Case _ e1,Case (LitPat (Bool b)) e2])
  | b         = Just (c,e2,e1)
  | otherwise = Just (c,e1,e2)
ifView (Match c [Case Default e1,Case (LitPat i@Int{}) e2])    = Just (c === literal i,e2,e1)
ifView (Match c (Case Default e1:Case (LitPat i@Int{}) e2:es)) = Just (c === literal i,e2,Match c (Case Default e1:es))
ifView _ = Nothing

projAt :: Expr a -> Maybe (Expr a,Expr a)
projAt (Builtin At :@: [a,b]) = Just (a,b)
projAt _                          = Nothing

projGlobal :: Expr a -> Maybe a
projGlobal (Gbl (Global x _ _) :@: []) = Just x
projGlobal _                           = Nothing

atomic :: Expr a -> Bool
atomic (_ :@: []) = True
atomic Lcl{}      = True
atomic _          = False

occurrences :: Eq a => Local a -> Expr a -> Int
occurrences var body = length (filter (== var) (universeBi body))

-- | The signature of a function
signature :: Function a -> Signature a
signature func@Function{..} = Signature func_name (funcType func)

-- | The type of a function
funcType :: Function a -> PolyType a
funcType (Function _ tvs lcls res _) = PolyType tvs (map lcl_type lcls) res

bound, free, locals :: Ord a => Expr a -> [Local a]
bound e =
  usort $
    concat [ lcls | Lam lcls _       <- universeBi e ] ++
           [ lcl  | Let lcl _ _      <- universeBi e ] ++
    concat [ lcls | Quant _ _ lcls _ <- universeBi e ] ++
    concat [ lcls | ConPat _ lcls    <- universeBi e ]
locals = usort . universeBi
free e = locals e \\ bound e

globals :: (UniverseBi (t a) (Global a),UniverseBi (t a) (Type a),Ord a)
        => t a -> [a]
globals e =
  usort $
    [ gbl_name | Global{..} <- universeBi e ] ++
    [ tc | TyCon tc _ <- universeBi e ]

tyVars :: Ord a => Type a -> [a]
tyVars t = usort $ [ a | TyVar a <- universeBi t ]

-- The free type variables are in the locals, and the globals:
-- but only in the types applied to the global variable.
freeTyVars :: Ord a => Expr a -> [a]
freeTyVars e =
  usort $
    concatMap tyVars $
             [ lcl_type | Local{..} <- universeBi e ] ++
      concat [ gbl_args | Global{..} <- universeBi e ]

-- | The type of an expression
exprType :: Ord a => Expr a -> Type a
exprType (Gbl (Global{..}) :@: _) = res
  where
    (_, res) = applyPolyType gbl_type gbl_args
exprType (Builtin blt :@: es) = builtinType blt (map exprType es)
exprType (Lcl lcl) = lcl_type lcl
exprType (Lam args body) = map lcl_type args :=>: exprType body
exprType (Match _ (Case _ body:_)) = exprType body
exprType (Match _ []) = ERROR("empty case expression")
exprType (Let _ _ body) = exprType body
exprType Quant{} = boolType

-- | The result type of a built in function, applied to some types
builtinType :: Ord a => Builtin -> [Type a] -> Type a
builtinType (Lit Int{}) _ = intType
builtinType (Lit Bool{}) _ = boolType
builtinType (Lit String{}) _ = ERROR("strings are not really here")
builtinType And _ = boolType
builtinType Or _ = boolType
builtinType Not _ = boolType
builtinType Implies _ = boolType
builtinType Equal _ = boolType
builtinType Distinct _ = boolType
builtinType NumAdd (ty:_) = ty
builtinType NumSub (ty:_) = ty
builtinType NumMul (ty:_) = ty
builtinType NumDiv (ty:_) = ty
builtinType IntDiv _ = intType
builtinType IntMod _ = intType
builtinType NumGt _ = boolType
builtinType NumGe _ = boolType
builtinType NumLt _ = boolType
builtinType NumLe _ = boolType
builtinType NumWiden _ = realType
builtinType At ((_  :=>: res):_) = res
builtinType At _ = ERROR("ill-typed lambda application")

theoryTypes :: (UniverseBi (t a) (Type a),Ord a) => t a -> [Type a]
theoryTypes = usort . universeBi

-- * Substition and refreshing

freshLocal :: Name a => Type a -> Fresh (Local a)
freshLocal ty = liftM2 Local fresh (return ty)

freshArgs :: Name a => Global a -> Fresh [Local a]
freshArgs gbl = mapM freshLocal (fst (gblType gbl))

refreshLocal :: Name a => Local a -> Fresh (Local a)
refreshLocal (Local name ty) = liftM2 Local (refresh name) (return ty)

-- Rename bound variables in an expression to fresh variables.
freshen :: Name a => Expr a -> Fresh (Expr a)
freshen e = freshenNames (map lcl_name (bound e)) e

freshenNames :: (TransformBi a (f a), Name a) =>
  [a] -> f a -> Fresh (f a)
freshenNames names e = do
  sub <- fmap (Map.fromList . zip names) (mapM refresh names)
  return . flip transformBi e $ \x ->
    case Map.lookup x sub of
      Nothing -> x
      Just y -> y

-- | Substitution, of local variables
--
-- Since there are only rank-1 types, bound variables from lambdas and
-- case never have a forall type and thus are not applied to any types.
(//) :: Name a => Expr a -> Local a -> Expr a -> Fresh (Expr a)
e // x = transformExprM $ \ e0 -> case e0 of
  Lcl y | x == y -> freshen e
  _              -> return e0

substMany :: Name a => [(Local a, Expr a)] -> Expr a -> Fresh (Expr a)
substMany xs e0 = foldM (\e (x,xe) -> (xe // x) e) e0 xs

letExpr :: Name a => Expr a -> (Local a -> Fresh (Expr a)) -> Fresh (Expr a)
letExpr (Lcl x) k = k x
letExpr b k =
  do v <- freshLocal (exprType b)
     rest <- k v
     return (Let v b rest)

-- | Substitution, but without refreshing. Only use when the replacement
-- expression contains no binders (i.e. no lambdas, no lets, no quantifiers),
-- since the binders are not refreshed at every insertion point.
unsafeSubst :: Ord a => Expr a -> Local a -> Expr a -> Expr a
e `unsafeSubst` _ | not (null (bound e)) = ERROR("unsafeSubst: contains binders")
e `unsafeSubst` x = transformExpr $ \ e0 -> case e0 of
  Lcl y | x == y -> e
  _              -> e0

-- * Making new locals and functions

updateLocalType :: Type a -> Local a -> Local a
updateLocalType ty (Local name _) = Local name ty

updateFuncType :: PolyType a -> Function a -> Function a
updateFuncType (PolyType tvs lclTys res) (Function name _ lcls _ body)
  | length lcls == length lclTys =
      Function name tvs (zipWith updateLocalType lclTys lcls) res body
  | otherwise = ERROR("non-matching type")


-- * Matching

matchTypesIn :: Ord a => [a] -> [(Type a, Type a)] -> Maybe [Type a]
matchTypesIn tvs tys = do
  sub <- matchTypes tys
  forM tvs $ \tv -> lookup tv sub

matchTypes :: Ord a => [(Type a, Type a)] -> Maybe [(a, Type a)]
matchTypes tys = mapM (uncurry match) tys >>= collect . usort . concat
  where
    match (TyVar x) ty = Just [(x, ty)]
    match (TyCon x tys1) (TyCon y tys2)
      | x == y && length tys1 == length tys2 =
        fmap concat (zipWithM match tys1 tys2)
    match (args1 :=>: res1) (args2 :=>: res2)
      | length args1 == length args2 =
        fmap concat (zipWithM match (res1:args1) (res2:args2))
    match ty1 ty2 | ty1 == ty2 = Just []
    match _ _ = Nothing

    collect [] = Just []
    collect [x] = Just [x]
    collect ((x, _):(y, _):_) | x == y = Nothing
    collect (x:xs) = fmap (x:) (collect xs)

makeGlobal :: Ord a => a -> PolyType a -> [Type a] -> Maybe (Type a) -> Maybe (Global a)
makeGlobal name polyty@PolyType{..} args mres = do
  vars <- matchTypesIn polytype_tvs tys
  return (Global name polyty vars)
  where
    tys =
      (case mres of Nothing -> []; Just res -> [(polytype_res, res)]) ++
      zip polytype_args args

-- * Data types

constructorType :: Datatype a -> Constructor a -> PolyType a
constructorType Datatype{..} Constructor{..} =
  PolyType data_tvs (map snd con_args) (TyCon data_name (map TyVar data_tvs))

destructorType :: Datatype a -> Type a -> PolyType a
destructorType Datatype{..} ty =
  PolyType data_tvs [TyCon data_name (map TyVar data_tvs)] ty

constructor :: Datatype a -> Constructor a -> [Type a] -> Global a
constructor dt con@Constructor{..} tys =
  Global con_name (constructorType dt con) tys

projector :: Datatype a -> Constructor a -> Int -> [Type a] -> Global a
projector dt Constructor{..} i tys =
  Global proj_name (destructorType dt proj_ty) tys
  where
    (proj_name, proj_ty) = case drop i con_args of ca:_ -> ca; [] -> __

discriminator :: Datatype a -> Constructor a -> [Type a] -> Global a
discriminator dt Constructor{..} tys =
  Global con_discrim (destructorType dt (BuiltinType Boolean)) tys

-- * Operations on theories

-- | Goals in first component, assertions in second
theoryGoals :: Theory a -> ([Formula a],[Formula a])
theoryGoals = partitionGoals . thy_asserts

-- | Goals in first component, assertions in second
partitionGoals :: [Formula a] -> ([Formula a],[Formula a])
partitionGoals = partition ((Prove ==) . fm_role)

mapDecls :: forall a b . (forall t . Traversable t => t a -> t b) -> Theory a -> Theory b
mapDecls k (Theory a b c d e) = Theory (map k a) (map k b) (map k c) (map k d) (map k e)

-- * Topologically sorting definitions

topsort :: (Ord a,Definition f) => [f a] -> [[f a]]
topsort = sortThings defines uses

class Definition f where
  defines :: f a -> a
  uses    :: f a -> [a]

data (f :+: g) a = InL (f a) | InR (g a)
  deriving (Eq,Ord,Show,Functor)

instance (Definition f,Definition g) => Definition (f :+: g) where
  defines (InL x) = defines x
  defines (InR y) = defines y
  uses (InL x) = uses x
  uses (InR y) = uses y

instance Definition Signature where
  defines = sig_name
  uses _  = []

instance Definition Function where
  defines = func_name
  uses    = F.toList . func_body

instance Definition Datatype where
  defines = data_name
  uses    = concatMap F.toList . data_cons

