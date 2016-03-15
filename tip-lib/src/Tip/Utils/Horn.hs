{-# LANGUAGE TypeFamilies, TypeSynonymInstances, FlexibleInstances, CPP, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Completing a set of horn clauses
module Tip.Utils.Horn (completeRules, specialiseRules, Expr(..), Rule(..)) where
import Twee.Base hiding (Var, Fun, App, Pretty)
import qualified Twee.Base as Twee
import qualified Twee.Index as Index
import Twee.Index(Index)
import Twee.Label
import Twee.Utils
import Control.Monad
import Data.Maybe
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap(IntMap)
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Data.Tuple
import Data.Foldable as F
import Data.Generics.Geniplate
import Tip.Pretty
import Text.PrettyPrint

data Clause a =
    Fact (Term a)
  | Term a :=>: Clause a
  deriving Eq

instance Symbolic (Clause a) where
  type ConstantOf (Clause a) = a
  term (Fact t) = t
  term (t :=>: _) = t
  termsDL (Fact t) = return (singleton t)
  termsDL (t :=>: c) = return (singleton t) `mplus` termsDL c
  replace f (Fact t) = Fact (replace f t)
  replace f (t :=>: c) = replace f t :=>: replace f c


complete :: [Clause a] -> [Clause a]
complete cs = Index.elems (foldr add Index.Nil cs)
  where
    add c idx
      | c `Index.elem` idx = idx
      | otherwise = derive c (Index.insert c idx)

    derive (Fact t) idx =
      foldr add idx [ c | _ :=>: c <- Index.lookup t (Index.freeze idx) ]
    derive (t :=>: r) idx =
      foldr add idx $ do
        Fact u <- Index.elems idx
        sub <- maybeToList (match t u)
        return (subst sub r)

data Expr c a = Var a | App c [Expr c a]
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance (Pretty c,Pretty a) => Pretty (Expr c a) where
  pp (Var x) = pp x
  pp (App c []) = pp c
  pp (App c as) = parens (pp c $\ fsep (map pp as))

data Rule c a = Expr c a :=> Rule c a | Fin (Expr c a)
  deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

instance (Pretty c,Pretty a) => Pretty (Rule c a) where
  pp (Fin e)   = pp e
  pp (e :=> r) = pp e <+> "=>" $\ pp r

return []

instanceUniverseBi  [t| forall c a . (Rule c a,c) |]
instanceTransformBi [t| forall c a . (Expr c a,[Rule c a]) |]
instanceTransformBi [t| forall c a . (Expr c a,Rule c a) |]
instanceTransformBi [t| forall c a . (Expr c a,Expr c a) |]

ruleHeads :: Rule c a -> [c]
ruleHeads = universeBi

specialiseRules :: Ord c => [Rule c Int] -> [Expr c Int]
specialiseRules = facts . completeRules
  where
  facts rs = [ e | Fin e <- rs, F.null e ]

completeRules :: Ord c => [Rule c Int] -> [Rule c Int]
completeRules rules =
  map ruleFromTwee (complete (map ruleToTwee rules))
  where
    numbers = zip [0..] (usort (concatMap ruleHeads rules))
    toMap = Map.fromList (map swap numbers)
    fromMap = IntMap.fromList numbers
    ruleToTwee (e :=> r) = build (exprToTwee e) :=>: ruleToTwee r
    ruleToTwee (Fin e) = Fact (build (exprToTwee e))
    exprToTwee (Var x) = var (MkVar x)
    exprToTwee (App h es) =
      fun (MkFun (Map.findWithDefault (error "completeRules") h toMap))
        (map exprToTwee es)
    ruleFromTwee (e :=>: r) = exprFromTwee e :=> ruleFromTwee r
    ruleFromTwee (Fact e) = Fin (exprFromTwee e)
    exprFromTwee (Twee.Var (MkVar x)) = Var x
    exprFromTwee (Twee.Fun (MkFun f) ts) =
      App (IntMap.findWithDefault (error "completeRules") f fromMap)
        (map exprFromTwee (fromTermList ts))

