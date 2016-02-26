{-# LANGUAGE PatternGuards,StandaloneDeriving,CPP #-}
module Tip.Id where

import Tip.Pretty
import Tip.Core

import Text.PrettyPrint (text)

import Name hiding (varName)
import OccName (occNameString)
-- import BasicTypes (TupleSort(..))
import PrelNames
import Tip.GHCUtils
import Var (Var,varName,idDetails,TyVar,tyVarName)
import IdInfo (IdDetails(..))
import TyCon (tyConName,TyCon)
import DataCon (dataConName,DataCon)
import Data.Char (toUpper)
import PrimOp

import TysWiredIn (trueDataCon,falseDataCon,boolTyCon)

idFromName :: Name -> Id
idFromName nm = GHCOrigin nm

idFromDataCon :: DataCon -> Id
idFromDataCon = idFromName . dataConName

idFromVar :: Var -> Id
idFromVar i = case idDetails i of
    DataConWorkId dc -> idFromDataCon dc
    DataConWrapId dc -> idFromDataCon dc
    _                -> idFromName (varName i)

idFromTyVar :: TyVar -> Id
idFromTyVar = idFromName . tyVarName

idFromTyCon :: TyCon -> Id
idFromTyCon tc = idFromName (tyConName tc)

tryGetGHCName :: Id -> Maybe Name
tryGetGHCName (GHCOrigin nm) = Just nm
tryGetGHCName _              = Nothing

-- | A representation of identifiers that come from GHC.
--
-- The 'PrettyVar' instance is one way to print the names.
data Id
    = GHCOrigin Name
    | Id `LiftedFrom` Id
    | Eta Int
    | Discrim Id
    | Project Id Int
    | Error
  deriving (Eq,Ord)

instance Show Id where
    show (GHCOrigin n)      = show (showOutputable n)
    show (Eta n)            = "eta" ++ show n
    show (Discrim c)        = "is-" ++ show c
    show (Project c i)      = show c ++ "_" ++ show i
    show (i `LiftedFrom` j) = show i ++ " `LiftedFrom` " ++ show j
    show Error              = "error"

instance PrettyVar Id where
    varStr = ppId

ppId :: Id -> String
ppId (GHCOrigin nm) = ppName nm
ppId (Eta n)        = "eta" ++ show n
ppId (Discrim c)    = "is-" ++ ppId c
ppId ((i `LiftedFrom` j) `LiftedFrom` k) = ppId (i `LiftedFrom` (j `LiftedFrom` k))
ppId (i `LiftedFrom` j)
  | Just nm <- tryGetGHCName i, isSystemName nm    = ppId j
  | ppId i /= ppId j && "prop_" /= take 5 (ppId j) = ppId j ++ "_" ++ ppId i
  | otherwise                                      = ppId i
ppId (Project c i)  = case (i,ppId c) of
                        (0,"Pair") -> "first"
                        (1,"Pair") -> "second"
                        (0,"cons") -> "head"
                        (1,"cons") -> "tail"
                        (0,"S")    -> "p"
                        (0,"Succ") -> "pred"
                        _          -> ppId c ++ "_" ++ show i
ppId Error = "error"

ppName :: Name -> String
ppName nm
    | k == listTyConKey      = "list"
    | k == nilDataConKey     = "nil"
    | k == consDataConKey    = "cons"
    | k == unitTyConKey      = "Unit"
    | k == genUnitDataConKey = "tt"
    | isSystemName nm        = "x"
    | otherwise = case getOccString nm of
        x | take 2 x == "ds"  -> "x"
        x | take 3 x == "ipv" -> "x"
        "(,)"  -> "Pair"
        "(,,)" -> "Triple"
        "+"   -> "plus"
        "-"   -> "minus"
        "/"   -> "div"
        "*"   -> "mult"
        "^"   -> "pow"
        "++"  -> "append"
        ">>=" -> "bind"
        "=<<" -> "dnib"
        ">=>" -> "dot_monadic"
        "<=<" -> "monadic_dot"
        "<*>" -> "ap"
        "<$>" -> "fmap"
        ">>"  -> "then"
        "||"  -> "or"
        "&&"  -> "and"
        "."   -> "dot"
        "=="  -> "equal"
        "/="  -> "unequal"
        ">"   -> "gt"
        ">="  -> "ge"
        "<"   -> "lt"
        "<="  -> "le"
        "$"   -> "apply"
        "!!"  -> "index"
        "\\\\" -> "difference"
        s     -> s
  where
    k = getUnique nm

primops :: [(PrimOp,Expr Id)]
primops =
  [ (ghc_op,Lam [int 0] (Lam [int 1] (Builtin tip_id :@: [Lcl (int 0),Lcl (int 1)])))
  | (ghc_op,tip_id) <-
    [ (IntAddOp, NumAdd)
    , (IntSubOp, NumSub)
    , (IntMulOp, NumMul)
    ]
  ] ++
#if __GLASGOW_HASKELL__ <= 706
  [ (ghc_op,Lam [int 0] (Lam [int 1] (Builtin tip_id :@: [Lcl (int 0),Lcl (int 1)])))
  | (ghc_op,tip_id) <-
    [ (IntEqOp, Equal)
    , (IntNeOp, Distinct)
    , (IntGtOp, NumGt)
    , (IntGeOp, NumGe)
    , (IntLtOp, NumLt)
    , (IntLeOp, NumLe)
    ]
  ]
#else
  [ (ghc_op,Lam [int 0] (Lam [int 1]
              (makeIf (Builtin tip_id :@: [Lcl (int 0),Lcl (int 1)])
                      (literal (Int 1)) (literal (Int 0)))))
  | (ghc_op,tip_id) <-
    [ (IntEqOp, Equal)
    , (IntNeOp, Distinct)
    , (IntGtOp, NumGt)
    , (IntGeOp, NumGe)
    , (IntLtOp, NumLt)
    , (IntLeOp, NumLe)
    ]
  ] ++
  [ (TagToEnumOp,Lam [int 0] (Match (Lcl (int 0))
                                [ Case Default          (bool False)
                                , Case (LitPat (Int 1)) (bool True)
                                ]))
  ]
#endif
 where
  int i = Local (Eta i) intType

