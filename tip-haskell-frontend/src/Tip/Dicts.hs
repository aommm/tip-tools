{-# LANGUAGE PatternGuards, TypeSynonymInstances, FlexibleInstances, ViewPatterns, ExplicitForAll #-}
{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleContexts, NamedFieldPuns #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Tip.Dicts (inlineDicts,maybeUnfolding) where

import Tip.GHCUtils (showOutputable)
#if __GLASGOW_HASKELL__ >= 708
import DynFlags (unsafeGlobalDynFlags)
#endif
import CoreSyn
import CoreUtils()
import IdInfo
import Id
import Var
import Data.List (elemIndex)
import VarEnv (emptyInScopeSet)

import Data.Generics.Geniplate

import Outputable
import Type
import Literal
import Coercion

import Name (getOccString,nameModule_maybe)
import PrelNames (gHC_REAL)

instanceTransformBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|AltCon|] ]
    [t| forall a . (Expr a,Expr a) |]

instanceTransformBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|AltCon|] ]
    [t| forall a . (Expr a,[Bind a]) |]

instanceTransformBiT
    [ [t|Var|], [t|Coercion|] , [t|Tickish Id|], [t|Literal|], [t|Type|], [t|AltCon|] ]
    [t| forall a . (Expr a,[(a,Expr a)]) |]

-- | Maybe the unfolding of an Id
maybeUnfolding :: Id -> Maybe CoreExpr
maybeUnfolding v = case ri of
    CoreUnfolding{uf_tmpl} -> Just uf_tmpl
    _                      -> Nothing
  where
    ri = realIdUnfolding v



inlineDicts :: TransformBi (Expr Id) t => t -> t
inlineDicts = transformBi $ \ e0 -> case e0 of
    App (App (Var f) (Type t)) (Var d)
        | getOccString f == "div" && nameModule_maybe (varName f) == Just gHC_REAL -> Var f
        | getOccString f == "mod" && nameModule_maybe (varName f) == Just gHC_REAL -> Var f
#if __GLASGOW_HASKELL__ >= 708
        | [try] <- [ try | BuiltinRule _ _ 2 try <- idCoreRules f ]
        , Just e <- try unsafeGlobalDynFlags (emptyInScopeSet,realIdUnfolding) f [Type t,Var d]
        -> e
#endif
        | Just cl <- isClassOpId_maybe f
        , DFunId{} <- idDetails d
        -> case maybeUnfolding f of
            Just (collectBinders -> (_,Case _ _ _ [(_,ss,Var s)]))
              | Just i <- elemIndex s ss -> case realIdUnfolding d of
#if __GLASGOW_HASKELL__ == 706
                DFunUnfolding _ _ es -> drop (length es - length ss) (dfunArgExprs es) !! i
#else
                DFunUnfolding _ _ es -> drop (length es - length ss) es !! i
#endif
                CoreUnfolding{uf_tmpl} ->
                    let (_,es) = collectArgs uf_tmpl
                    in  drop (length es - length ss) es !! i
                x -> e0 -- error $ showOutputable (e0,x)
            x -> e0 -- error $ showOutputable (e0,x)
    _ -> e0


