-- | the abstract syntax
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE ExplicitForAll, FlexibleContexts, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
module Tip.Types where

import Data.Generics.Geniplate
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Monoid

import Control.Monad.State.Lazy

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (catMaybes)

import Text.Regex.TDFA

import Debug.Trace

data Head a
  = Gbl (Global a)
  | Builtin Builtin
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Local a = Local { lcl_name :: a, lcl_type :: Type a }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Global a = Global
  { gbl_name      :: a
  , gbl_type      :: PolyType a
  , gbl_args      :: [Type a]
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

infix 5 :@:

data Expr a
  = Head a :@: [Expr a]
  -- ^ Function application: always perfectly saturated.
  --   Lambdas and locals are applied with 'At' as head.
  | Lcl (Local a)
  | Lam [Local a] (Expr a)
  -- Merge with Quant?
  | Match (Expr a) [Case a]
  -- ^ The default case comes first if there is one
  | Let (Local a) (Expr a) (Expr a)
  -- ^ @Let (Local x t) b e@ = @(let ((l x)) b e)@
  -- Unlike SMT-LIB, this does not accept a list of bound
  -- variable-/expression-pairs. Fix?
  | Quant QuantInfo Quant [Local a] (Expr a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Quant = Forall | Exists
  deriving (Eq,Ord,Show)

data QuantInfo = NoInfo | QuantIH Int
  deriving (Eq,Ord,Show)

data Case a = Case { case_pat :: Pattern a, case_rhs :: Expr a }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Builtin
  = At
  | Lit Lit
  | And
  | Or
  | Not
  | Implies
  | Equal
  | Distinct
  | IntAdd
  | IntSub
  | IntMul
  | IntDiv
  | IntMod
  | IntGt
  | IntGe
  | IntLt
  | IntLe
  deriving (Eq,Ord,Show)

intBuiltin :: Builtin -> Bool
intBuiltin b = b `elem` [IntAdd,IntSub,IntMul,IntDiv,IntMod,IntGt,IntGe,IntLt,IntLe]

litBuiltin :: Builtin -> Bool
litBuiltin Lit{} = True
litBuiltin _     = False

eqRelatedBuiltin :: Builtin -> Bool
eqRelatedBuiltin b = b `elem` [Equal,Distinct]

logicalBuiltin :: Builtin -> Bool
logicalBuiltin b = b `elem` [And,Or,Implies,Equal,Distinct,Not]

data Lit
  = Int Integer
  | Bool Bool
  | String String -- Not really here but might come from GHC
  deriving (Eq,Ord,Show)

-- | Patterns in branches
data Pattern a
  = Default
  | ConPat { pat_con  :: Global a, pat_args :: [Local a] }
  | LitPat Lit
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Polymorphic types
data PolyType a =
  PolyType
    { polytype_tvs  :: [a]
    , polytype_args :: [Type a]
    , polytype_res  :: Type a
    }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Types
data Type a
  = TyVar a
  | TyCon a [Type a]
  | [Type a] :=>: Type a
  | BuiltinType BuiltinType
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data BuiltinType
  = Integer | Boolean
  deriving (Eq,Ord,Show)

data Function a = Function
  { func_name :: a
  , func_tvs  :: [a]
  , func_args :: [Local a]
  , func_res  :: Type a
  , func_body :: Expr a
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Uninterpreted function
data Signature a = Signature
  { sig_name :: a
  , sig_type :: PolyType a
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Uninterpreted sort
data Sort a = Sort
  { sort_name :: a
  , sort_tvs  :: [a] }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | Data definition
data Datatype a = Datatype
  { data_name :: a
  , data_tvs  :: [a]
  , data_cons :: [Constructor a]
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Constructor a = Constructor
  { con_name    :: a
  -- ^ Constructor name (e.g. @Cons@)
  , con_discrim :: a
  -- ^ Discriminator name (e.g. @is-Cons@)
  , con_args    :: [(a,Type a)]
  -- ^ Argument types names of their projectors
  --   (e.g. [(@head@,a),(@tail@,List a)])
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Theory a = Theory
  { thy_datatypes   :: [Datatype a]
  , thy_sorts       :: [Sort a]
  , thy_sigs        :: [Signature a]
  , thy_funcs       :: [Function a]
  , thy_asserts     :: [Formula a]
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

emptyTheory :: Theory a
emptyTheory = Theory [] [] [] [] []

joinTheories :: Theory a -> Theory a -> Theory a
joinTheories (Theory a o e u i) (Theory s n t h d) = Theory (a++s) (o++n) (e++t) (u++h) (i++d)

instance Monoid (Theory a) where
  mempty  = emptyTheory
  mappend = joinTheories

data Formula a = Formula
  { fm_role :: Role
  , fm_info :: Info a
  , fm_tvs  :: [a]
  -- ^ top-level quantified type variables
  , fm_body :: Expr a
  }
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

getFmName :: Formula a -> Maybe String
getFmName (Formula _ (UserAsserted name) _ _) = name
getFmName (Formula _ (Lemma _ name _) _ _) = name
getFmName _ = error "getFmName: can only get name from UserAsserted and Lemma"

setFmName :: String -> Formula a -> Formula a
setFmName name (Formula a (UserAsserted _) b c) = Formula a (UserAsserted (Just name)) b c
setFmName name (Formula a (Lemma b _ c) d e) = Formula a (Lemma b (Just name) c) d e
setFmName _ _ = error "setFmName: can only set name to UserAsserted and Lemma"

-- lemmas used
-- coords on which we did induction
type ProofSketch = ([String],[Int])


-------------------------------------------------------------------------------
-- Library
-- (Should maybe be moved to separate file)

-- Thoughts: 
-- Since we can always convert Library->Theory and Theory->Library,
-- Library is not really existensberättigad

-- Thoughts regarding saving functions/datatypes/lemmas:
-- These things contain references to things, e.g. variables, other functions, other lemmas
-- What kind of things do we keep references to?
-- How to keep internal consistency,
-- when e.g. two different TIP problems refer to the same function,
-- or when a lemma refers to another lemma?

-- Note regarding types of keys:
-- Fns/datas indexed by their 'name'
-- Lemmas indexed by string (so that we can generate new ones)
data Library a = Library
  { lib_funcs :: Map a (Function a)
  , lib_datatypes :: Map a (Datatype a)
  , lib_lemmas :: Map String (Formula a)
  -- lib_sigs
  -- lib_sorts
  }
  deriving (Eq,Ord,Show)

emptyLibrary :: Library a
emptyLibrary = Library M.empty M.empty M.empty

joinLibraries ::(Ord a) => Library a -> Library a -> Library a
joinLibraries (Library a b c) (Library x y z) = Library (a `M.union` x) (b `M.union` y) (c `M.union` z)

-- for fun
instance Ord a => Monoid (Library a) where
  mempty  = emptyLibrary
  mappend = joinLibraries

-- | Extends a library with the fns/datatypes/lemmas of a theory
extendLibrary :: (Ord a, Show a) => Theory a -> Library a -> Library a
extendLibrary thy lib = runLibrary (initLibrary lib) $ do
                 mapM_ addFunction (thy_funcs thy)
                 mapM_ addDatatype (thy_datatypes thy) 
                 mapM_ addLemma (thy_asserts thy)
                 translateLemmaRefs

-- | Creates a library from a theory
thyToLib :: (Ord a, Show a) => Theory a -> Library a
thyToLib thy = runLibrary emptyLibraryState $ do
                 mapM_ addFunction (thy_funcs thy)
                 mapM_ addDatatype (thy_datatypes thy) 
                 mapM_ addLemma (thy_asserts thy)
                 translateLemmaRefs

-- | Creates a theory from a library
libToThy :: (Ord a, Show a) => Library a -> Theory a
libToThy lib = emptyTheory {
  thy_datatypes = M.elems (lib_datatypes lib),
  thy_funcs = M.elems (lib_funcs lib),
  thy_asserts = M.elems (lib_lemmas lib)
}

type LibraryMonad a b = State (LibraryState a) b
data LibraryState a = LibraryState
  { libs_lib :: Library a
  , libs_next :: Int
  , libs_lemmaTranslations :: Map String String
  -- ^ lemma translations to do, oldName->newName map
  -- will be search-and-replaced in proof output
  }

emptyLibraryState :: LibraryState a
emptyLibraryState = LibraryState emptyLibrary 0 M.empty

-- | Calculates a LibraryState given a Library
-- (State includes next free variable and a library)
initLibrary :: (Ord a, Show a, Eq a) => Library a -> LibraryState a
initLibrary l = LibraryState l next M.empty -- TODO empty translat?
  where next = let ks = M.keys (lib_lemmas l)
                   regexs = map regexName ks
                   matches = map (\(_,_,_,grps) -> grps) regexs
                   numbers = (catMaybes.map getNumbers) matches
                   number = if null numbers
                              then 0
                              else maximum numbers + 1
               in trace ("numbers:"++show numbers) $ number
        getNumbers [i] = Just (read i :: Int)
        getNumbers _   = Nothing
        regexName s = s =~ "lemma-([0-9]+)" :: (String,String,String,[String])


runLibrary :: LibraryState a -> LibraryMonad a b -> Library a
runLibrary init s = libs_lib $ execState s init

addFunction :: (Show a, Eq a, Ord a) => Function a -> LibraryMonad a ()
addFunction f = do
  LibraryState lib next ts <- get
  let name = (func_name f)
  let fns = (lib_funcs lib)
  let fns' =
        case M.lookup name fns of
          Nothing -> trace "add new function" $ M.insert name f fns
          Just f' ->
            if f == f' -- TODO: compare "normalised" variants of fns. Then != truly means !=
              then trace "function existed" $ fns
              else trace "function existed with different definition, doing nothing" $ fns
              --else error $ "cannot add function: function "++ show name ++" already exists, but with different definition" ++ show f ++ "\n" ++ show f'
  put $ LibraryState (lib {lib_funcs=fns'}) next ts

addDatatype :: (Show a, Eq a, Ord a) => Datatype a -> LibraryMonad a ()
addDatatype d = do
  LibraryState lib next ts <- get
  let name = (data_name d)
  let datas = (lib_datatypes lib)
  let datas' =
        case M.lookup name datas of
          Nothing -> trace "add new datatype" $ M.insert name d datas
          Just d' ->
            if d == d'
              then trace "datatype existed" $ datas
              else error $ "cannot add datatype: datatype "++ show name ++" already exists, but with different definition"
  put $ LibraryState (lib {lib_datatypes=datas'}) next ts
  --put (lib {lib_datatypes=datas'}, next)

-- TODO: we wanna be able to change the lemma, in case it already exists but with a different name.
-- then we want to rename it. How to accomplish this?

-- When we change a lemma's name (from either Just x or Nothing),
-- we want to rename it in the rest of the theory (i.e. in proof output)
addLemma :: (Show a, Eq a, Ord a) => Formula a -> LibraryMonad a ()
addLemma f =  do
  LibraryState lib _ _ <- get
  -- TODO: always call generateNewName, in case user supplied name is nonunique. call generateName or smth
  
  -- TODO 2: check if lemma already exists, dude!
  -- Outline:

  -- if lemma has name:
    -- if lemma with identical name and identical body exists:
      -- do nothing
    -- if lemma with identical name and nonidentical body exists:
      -- goto 0
    -- else, no identical name:
      -- add lemma

  -- else, lemma has no name:
    -- goto 0

  -- 0:
    -- if lemma with identical body exists:
      -- changeName to that name, add lemma
    -- else, no identical body exists:
      -- changeName to new name, add lemma


  name <- case fm_info f of
    UserAsserted (Just name) -> return name
    UserAsserted Nothing -> generateNewName
    Lemma _ (Just name) _ -> return name
    Lemma _ Nothing _ -> generateNewName
  let info = case fm_info f of
               UserAsserted _ -> UserAsserted (Just name)
               Lemma a _ b    -> Lemma a (Just name) b
      f' = f {fm_info = info}
      lemmas = lib_lemmas lib
      lemmas' = case M.lookup name lemmas of
                  Just n  -> error "generateNewName failed, name is already occupied"
                  Nothing -> trace "add new lemma" $ M.insert name f' lemmas
  LibraryState _ next ts <- get -- was maybe updated by generateNewName
  put $ LibraryState (lib {lib_lemmas=lemmas'}) next ts

-- | Change name of f to name, returning the new lemma
-- If it already had a name, adds name change to 'to be translated' list
-- TODO
changeName :: (Show a, Eq a, Ord a) => Formula a -> String -> LibraryMonad a (Formula a)
changeName f newName = do
  let oldName = getFmName f
      f' = setFmName newName f
  case oldName of
    Nothing -> return ()
    -- Add pair to lemmaTranslations
    Just n  -> do
      state <- get
      let translations = M.insert n newName (libs_lemmaTranslations state) 
      put $ state {libs_lemmaTranslations = translations}
  return f'

--doesLemmaExist :: (Show a, Eq a, Ord a) => (Maybe String) -> Formula a -> LibraryMonad a Boolean
--doesLemmaExist name f = do
--  (lib,_) <- get
--  let lemmas = lib_lemmas lib
--  M.lookup name lemmas

-- | Returns a free name, and increments the internal name counter
-- TODO change?
generateNewName :: LibraryMonad a String
generateNewName = do
  LibraryState lib next ts <- get
  put $ LibraryState lib (next+1) ts
  let name = "lemma-" ++ show next
  -- TODO: inefficient, for each name we will loop through all lemmas to see if it's taken
  -- In future: some kind init :: Library a -> LibraryMonad a ()
  -- which loops through a library (probably read from file) and finds out the next free name.
  -- not foolproof though
  case M.lookup name (lib_lemmas lib) of
    Nothing -> trace ("new name:"++show name) $ return name
    Just _  -> generateNewName
  
-- | Translates all lemma proofs with the libs_lemmaTranslations translator, emptying it when done
-- TODO
translateLemmaRefs :: LibraryMonad a ()
translateLemmaRefs = do
  state <- get
  let lemmas = (lib_lemmas . libs_lib) state
  lemmas' <- sequence $ (flip M.mapWithKey) (libs_lemmaTranslations state) $ \from -> \to ->
    return lemmas
    -- TODO 
    --forM lemmas (updateLemma from to) 


  return ()

  where
    updateLemma :: String -> String -> Formula a -> Formula a
    updateLemma from to (Formula a (Lemma b c mp) e f) = Formula a (Lemma b c (updateProof from to mp)) e f
    updateProof :: String -> String -> Maybe ProofSketch -> Maybe ProofSketch 
    updateProof from to (Just (lemmas, coords)) = Just (lemmas', coords)
      where lemmas' = replace from to lemmas


replace :: Eq a => a -> a -> [a] -> [a]
replace from to (x:xs) | x == from = to : replace from to xs
replace from to (x:xs) | otherwise = x  : replace from to xs
replace _    _  [] = []

-------------------------------------------------------------------------------



data Info a
  = Definition a
  | IH Int
  | Lemma Int (Maybe String) (Maybe ProofSketch) -- name of lemma
  | Projection a
  | DataDomain a
  | DataProjection a
  | DataDistinct a
  | Defunction a
  | UserAsserted (Maybe String) -- name of lemma
  | Unknown
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

data Role = Assert | Prove
  deriving (Eq,Ord,Show)

-- * Other views of theories

-- | The different kinds of declarations in a 'Theory'.
data Decl a
    = DataDecl (Datatype a)
    | SortDecl (Sort a)
    | SigDecl (Signature a)
    | FuncDecl (Function a)
    | AssertDecl (Formula a) -- rename to FormulaDecl?
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

-- | 'Decl'arations in a 'Theory'
theoryDecls :: Theory a -> [Decl a]
theoryDecls (Theory{..}) =
    map DataDecl thy_datatypes ++
    map SortDecl thy_sorts ++
    map SigDecl thy_sigs ++
    map FuncDecl thy_funcs ++
    map AssertDecl thy_asserts

-- | Assemble a 'Theory' from some 'Decl'arations
declsToTheory :: [Decl a] -> Theory a
declsToTheory ds = Theory
    { thy_datatypes = [ d | DataDecl d   <- ds ]
    , thy_sorts     = [ d | SortDecl d   <- ds ]
    , thy_sigs      = [ d | SigDecl d    <- ds ]
    , thy_funcs     = [ d | FuncDecl d   <- ds ]
    , thy_asserts   = [ d | AssertDecl d <- ds ]
    }

declsPass :: ([Decl a] -> [Decl b]) -> Theory a -> Theory b
declsPass k = declsToTheory . k . theoryDecls

-- Instances

instanceUniverseBi [t| forall a . (Expr a,Expr a) |]
instanceUniverseBi [t| forall a . (Function a,Expr a) |]
instanceUniverseBi [t| forall a . (Function a,Global a) |]
instanceUniverseBi [t| forall a . (Function a,Type a) |]
instanceUniverseBi [t| forall a . (Datatype a,Type a) |]
instanceUniverseBi [t| forall a . (Expr a,Pattern a) |]
instanceUniverseBi [t| forall a . (Expr a,Local a) |]
instanceUniverseBi [t| forall a . (Expr a,Global a) |]
instanceUniverseBi [t| forall a . (Theory a,Expr a) |]
instanceUniverseBi [t| forall a . (Theory a,Type a) |]
instanceUniverseBi [t| forall a . (Type a,Type a) |]
instanceUniverseBi [t| forall a . (Theory a,Constructor a) |]
instanceUniverseBi [t| forall a . (Theory a,Global a) |]
instanceUniverseBi [t| forall a . (Theory a,Local a) |]
instanceUniverseBi [t| forall a . (Theory a,Builtin) |]
instanceTransformBi [t| forall a . (Expr a,Expr a) |]
instanceTransformBi [t| forall a . (a,Expr a) |]
instanceTransformBi [t| forall a . (a,Formula a) |]
instanceTransformBi [t| forall a . (Expr a,Function a) |]
instanceTransformBi [t| forall a . (Expr a,Theory a) |]
instanceTransformBi [t| forall a . (Head a,Expr a) |]
instanceTransformBi [t| forall a . (Head a,Theory a) |]
instanceTransformBi [t| forall a . (Local a,Expr a) |]
instanceTransformBi [t| forall a . (Pattern a,Expr a) |]
instanceTransformBi [t| forall a . (Pattern a,Theory a) |]
instanceTransformBi [t| forall a . (Type a,Theory a) |]
instanceTransformBi [t| forall a . (Global a,Theory a) |]
instanceTransformBi [t| forall a . (Type a,Decl a) |]
instanceTransformBi [t| forall a . (Type a,Expr a) |]
instanceTransformBi [t| forall a . (Type a,Type a) |]
instance Monad m => TransformBiM m (Expr a) (Expr a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Expr a) (Function a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Function a -> m (Function a) |])
instance Monad m => TransformBiM m (Pattern a) (Expr a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Pattern a -> m (Pattern a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Local a) (Expr a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Local a -> m (Local a)) -> Expr a -> m (Expr a) |])
instance Monad m => TransformBiM m (Expr a) (Theory a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Theory a -> m (Theory a) |])
instance Monad m => TransformBiM m (Expr a) (Formula a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Expr a -> m (Expr a)) -> Formula a -> m (Formula a) |])
instance Monad m => TransformBiM m (Type a) (Type a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Type a -> m (Type a)) -> Type a -> m (Type a) |])
instance Monad m => TransformBiM m (Type a) (Theory a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Type a -> m (Type a)) -> Theory a -> m (Theory a) |])
instance Monad m => TransformBiM m (Function a) (Theory a) where
  {-# INLINE transformBiM #-}
  transformBiM = $(genTransformBiM' [t| forall m a . (Function a -> m (Function a)) -> Theory a -> m (Theory a) |])

transformExpr :: (Expr a -> Expr a) -> Expr a -> Expr a
transformExpr = transformBi

transformExprM :: Monad m => (Expr a -> m (Expr a)) -> Expr a -> m (Expr a)
transformExprM = transformBiM

transformExprIn :: TransformBi (Expr a) (f a) => (Expr a -> Expr a) -> f a -> f a
transformExprIn = transformBi

transformExprInM :: TransformBiM m (Expr a) (f a) => (Expr a -> m (Expr a)) -> f a -> m (f a)
transformExprInM = transformBiM

transformType :: (Type a -> Type a) -> Type a -> Type a
transformType = transformBi

transformTypeInExpr :: (Type a -> Type a) -> Expr a -> Expr a
transformTypeInExpr =
  $(genTransformBiT' [[t|PolyType|]] [t|forall a. (Type a -> Type a) -> Expr a -> Expr a|])

transformTypeInDecl :: (Type a -> Type a) -> Decl a -> Decl a
transformTypeInDecl =
  $(genTransformBiT' [[t|PolyType|]] [t|forall a. (Type a -> Type a) -> Decl a -> Decl a|])


