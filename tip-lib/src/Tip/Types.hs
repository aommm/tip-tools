-- | the abstract syntax
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, PatternGuards #-}
{-# LANGUAGE ExplicitForAll, FlexibleContexts, FlexibleInstances, TemplateHaskell, MultiParamTypeClasses #-}
module Tip.Types where

import Data.Generics.Geniplate
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Monoid
import Data.Ratio

import Control.Monad.State.Lazy

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromJust)

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
  | NumAdd
  | NumSub
  | NumMul
  | NumDiv
  | IntDiv
  | IntMod
  | NumGt
  | NumGe
  | NumLt
  | NumLe
  | NumWiden
  deriving (Eq,Ord,Show)

numBuiltin :: Builtin -> Bool
numBuiltin b = b `elem` [NumAdd,NumSub,NumMul,NumDiv,IntDiv,IntMod,NumGt,NumGe,NumLt,NumLe,NumWiden]

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
  = Integer | Real | Boolean
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
getFmName _ = Nothing --error "getFmName: can only get name from UserAsserted and Lemma"

setFmName :: String -> Formula a -> Formula a
setFmName name (Formula a (UserAsserted _) b c) = Formula a (UserAsserted (Just name)) b c
setFmName name (Formula a (Lemma b _ c) d e) = Formula a (Lemma b (Just name) c) d e
setFmName _ _ = error "setFmName: can only set name to UserAsserted and Lemma"

equalModInfo :: Eq a => Formula a -> Formula a -> Bool
equalModInfo (Formula r1 _ t1 b1) (Formula r2 _ t2 b2) = r1 == r2 && t1 == t2 && b1 == b2

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

joinLibraries ::(Ord a, Show a, Eq a) => Library a -> Library a -> Library a
joinLibraries l1 l2 = runLibrary (initLibrary l1) $ do
  -- get next free name from l1
  state1 <- get
  let next1 = libs_next state1
      next2 = nextFreeVar l2
      next  = max next1 next2
      -- TODO: remove gap in lemma names
      -- now e.g. {l1 l2} + {l3 l4 l5} = {l1 l2 l6 l7 l8}
      state2 = runLibraryState (initLibrary l2) $ do
                                                      -- set it to be next free name in l2
                                                      state2 <- get
                                                      put $ state2 {libs_next = next}
                                                      -- rename everything in l2 by removing all, then re-adding
                                                      lemmas <- getLemmas
                                                      setLemmas M.empty
                                                      forM_ lemmas $ \lemma -> do
                                                        name <- generateNewName
                                                        lemma' <- changeName lemma name
                                                        addLemma lemma'
                                                      commitLemmas
  -- last free name in l2 is now in l1 also
  put state1 {libs_next = libs_next state2 }
  -- join l1 and l2, by addFunction, addDatatype, addLemma into l1 from l2
  let l2' = libs_lib state2
  mapM_ addFunction (lib_funcs l2')
  mapM_ addDatatype (lib_datatypes l2') 
  mapM_ addLemma (lib_lemmas l2')
  commitLemmas

-- for fun
instance (Ord a,Show a,Eq a) => Monoid (Library a) where
  mempty  = emptyLibrary
  mappend = joinLibraries

-- | Extends a library with the fns/datatypes/lemmas of a theory
extendLibrary :: (Ord a, Show a) => Theory a -> Library a -> Library a
extendLibrary thy lib = 
  let thyLib = thyToLib thy
  in lib `joinLibraries` thyLib

-- | Creates a library from a theory
thyToLib :: (Ord a, Show a) => Theory a -> Library a
thyToLib thy = runLibrary emptyLibraryState $ do
                 mapM_ addFunction (thy_funcs thy)
                 mapM_ addDatatype (thy_datatypes thy) 
                 mapM_ addLemma (thy_asserts thy)
                 commitLemmas

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
  , libs_lemmaQueue :: Map String (Formula a)
  -- ^ lemmas which are in the process of being added
  -- only these will be modified in search-and-replace stage
  }

emptyLibraryState :: LibraryState a
emptyLibraryState = LibraryState emptyLibrary 0 M.empty M.empty

-- | Calculates a LibraryState from a Library
-- (State includes next free variable and a library)
initLibrary :: (Ord a, Show a, Eq a) => Library a -> LibraryState a
initLibrary l = emptyLibraryState {libs_next = next, libs_lib = l}
  where next = nextFreeVar l

runLibrary :: LibraryState a -> LibraryMonad a b -> Library a
runLibrary init s = libs_lib $ execState s init

runLibraryState :: LibraryState a -> LibraryMonad a b -> LibraryState a
runLibraryState init s = execState s init

getLemmas :: LibraryMonad a (Map String (Formula a))
getLemmas = do
  libState <- get
  return $ (lib_lemmas . libs_lib) libState

setLemmas :: Map String (Formula a) -> LibraryMonad a ()
setLemmas lemmas = do
  libState <- get
  let lib = libs_lib libState
      lib' = lib {lib_lemmas = lemmas}
      libState' = libState {libs_lib = lib'}
  put libState'

nextFreeVar :: (Ord a, Show a, Eq a) => Library a -> Int
nextFreeVar l = let ks = M.keys (lib_lemmas l)
                    regexs = map regexName ks
                    matches = map (\(_,_,_,grps) -> grps) regexs
                    numbers = (catMaybes.map getNumbers) matches
                    number = if null numbers
                              then 0
                              else maximum numbers + 1
                in trace ("numbers:"++show numbers) $ number
  where 
    getNumbers [i] = Just (read i :: Int)
    getNumbers _   = Nothing
    regexName s = s =~ "lemma-([0-9]+)" :: (String,String,String,[String])

addFunction :: (Show a, Eq a, Ord a) => Function a -> LibraryMonad a ()
addFunction f = do
  LibraryState lib next ts lq <- get
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
  put $ LibraryState (lib {lib_funcs=fns'}) next ts lq

addDatatype :: (Show a, Eq a, Ord a) => Datatype a -> LibraryMonad a ()
addDatatype d = do
  LibraryState lib next ts lq <- get
  let name = (data_name d)
  let datas = (lib_datatypes lib)
  let datas' =
        case M.lookup name datas of
          Nothing -> trace "add new datatype" $ M.insert name d datas
          Just d' ->
            if d == d'
              then trace "datatype existed" $ datas
              else error $ "cannot add datatype: datatype "++ show name ++" already exists, but with different definition"
  put $ LibraryState (lib {lib_datatypes=datas'}) next ts lq


-- | Adds a lemma to queue.
-- Checks if the lemma already exists. Maybe changes the lemma's name to a new or existing one
-- If the lemma's name is changed, the name change is added to libs_lemmaTranslations
-- Changes should be committed

-- if lemma has name:
  -- if lemma with identical name and identical body exists:
    -- do nothing
  -- if lemma with identical name and nonidentical body exists:
    -- goto checkAllLemmas
  -- else, no identical name:
    -- goto checkAllLemmas (?)
-- else, lemma has no name:
  -- goto checkAllLemmas

-- checkAllLemmas:
  -- if lemma with identical body exists:
    -- changeName to that name
  -- else, no identical body exists:
    -- changeName to new name, add lemma

addLemma :: (Show a, Eq a, Ord a) => Formula a -> LibraryMonad a ()
addLemma f =  do
  libState <- get
  let lib = libs_lib libState
      lemmas = lib_lemmas lib
  case getFmName f of
      Just n  -> do
        case M.lookup n lemmas of
          Just f' | f `equalModInfo` f' -> trace ("add lemma with name "++show n ++",already existed, equal body") $ return ()
                  | otherwise -> trace ("add lemma with name "++show n ++",already existed, nonequal body"{-++show f ++ show f'-} ) $ checkAllLemmas f Nothing
          Nothing -> trace ("add lemma with name "++show n ++",not already existed") $ checkAllLemmas f (Just n)
      Nothing -> trace ("add lemma with no name") $ checkAllLemmas f Nothing
  where
    -- Unconditionally add lemma to queue
    addLemma' f = do
      libState <- get
      let lemmaQ    = libs_lemmaQueue libState
          name      = fromJust $ getFmName f
          lemmaQ'   = M.insert name f lemmaQ
          libState' = libState { libs_lemmaQueue = lemmaQ' }
      put libState'
    -- Loop through all lemmas, see if formula's body exists anywhere
    checkAllLemmas f mname = do
      libState <- get
      let lemmas = lib_lemmas (libs_lib libState)
          matchingLemmas = M.filter (equalModInfo f) lemmas
      case M.size matchingLemmas of 
        0 -> do
          name <- case mname of
            Nothing   -> generateNewName
            Just name -> return name
          f' <- changeName f name
          trace ("  equal body not found, new name: "++show name) $ addLemma' f'
        1 -> do
          let name = head (M.keys matchingLemmas) -- existing name
          changeName f name
          trace ("  equal body found, name: "++show name) $ return ()
          -- TODO: that formula and our formula may have been proven differently
          -- which proof is the simplest? Or should we store both proofs?
        _ -> error $ "Multiple identical lemmas found, equal to "++show f 


-- | Change name of f to name, returning the new lemma
-- If it already had a name, adds name change to 'to be translated' list
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

-- | Returns a free name, and increments the internal name counter
generateNewName :: LibraryMonad a String
generateNewName = do
  LibraryState lib next ts lq <- get
  put $ LibraryState lib (next+1) ts lq
  let name = "lemma-" ++ show next
  -- TODO: inefficient, for each name we will loop through all lemmas to see if it's taken
  -- Should simply remove lookup, I think we can assume that it doesn't already exist
  case M.lookup name (lib_lemmas lib) of
    Nothing -> trace ("new name:"++show name) $ return name
    Just _  -> generateNewName
  
-- | Translates all lemma proofs with the libs_lemmaTranslations translator, emptying it when done
-- Also transfers lemmas from queue to real lemmas
-- TODO rename to 'commitLemmas' or something similar?
commitLemmas :: LibraryMonad a ()
commitLemmas = do
  state <- get
  let lemmaQ = libs_lemmaQueue state
      lemmaQ' = (flip M.map) lemmaQ $ \lemma ->
        M.foldrWithKey updateLemma lemma (libs_lemmaTranslations state)
      lib = libs_lib state
      lemmas' = M.union (lib_lemmas lib) lemmaQ'
      lib' = lib {lib_lemmas = lemmas'}
      state' = state {libs_lemmaTranslations = M.empty, libs_lemmaQueue = M.empty, libs_lib = lib'}
  -- TODO: enough to update proof output? When are names updated (and keys of map for that matter)?
  put state'

  where
    updateLemma :: String -> String -> Formula a -> Formula a
    updateLemma from to (Formula a (Lemma b c mp) e f) =mebeTrace $ Formula a (Lemma b c (updateProof from to mp)) e f
      where mebeTrace =  id -- (if from /= to then (trace $ "updating "++from++" to "++to) else id)
    updateLemma from to f = f
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


