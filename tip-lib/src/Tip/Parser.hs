-- | Parses the TIP format
module Tip.Parser(parse,parseFile,parseLibrary,Id,idPos) where

import Data.Monoid

import Tip.Parser.ParTIP
import Tip.Parser.AbsTIP (Start(..))
import Tip.Parser.ErrM

import Tip.Parser.Convert

import qualified Tip.Parser.ParTIPProof as PP
import qualified Tip.Parser.AbsTIPProof as PA (Start(..))
import qualified Tip.Parser.ConvertProof as PC

import Tip.Core

-- | Parse from a file. If the string is empty or "-", then reads from stdin.
parseFile :: String -> IO (Either String (Theory Id))
parseFile file =
  do s <- case file of
       ""  -> getContents
       "-" -> getContents
       _   -> readFile file
     return (parse s)

-- | Parse, and get either an error or the string's theory
parse :: String -> Either String (Theory Id)
parse s =
  case pStart . myLexer $ s of
    Ok (Start ds) -> runCM (trDecls ds)
    Bad err       -> Left err

-- | Parse, and get either an error or the string's library
parseLibrary :: String -> Either String (Library Id)
parseLibrary s =
  case PP.pStart . PP.myLexer $ s of
    Ok (PA.Start ds) -> PC.runCM (PC.trDecls ds)
    Bad err       -> Left err

---- | Parse, and get either an error or the string's theory
--parseProof :: String -> Either String (Theory Id)
--parseProof s =
--  case PP.pStart . PP.myLexer $ s of
--    Ok (PA.Start ds) -> runCM (PC.trDeclsProof ds)
--    Bad err          -> Left err

