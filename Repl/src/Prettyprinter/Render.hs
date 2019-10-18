{-# LANGUAGE LambdaCase #-}
module Prettyprinter.Render
  (
    datatypesToMyDoc,
    codatatypesToMyDoc,
    exprToMyDoc,
    progToMyDoc,
    docToString,
    docToTerminal
  ) where

import Control.Monad.Reader
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String
import qualified Data.Text as T
import System.Console.ANSI

import AST
import Prettyprinter.Definitions
import Prettyprinter.Expressions
import Prettyprinter.Declarations
import ProgramDef
import Renamer.DeBruijnToNamed (deBruijnToNamed)
import Renamer.CoqToDeBruijn (coqToDeBruijn)
import Skeleton

{--------------------------------------------
----Custom Backend for Console---------------
--------------------------------------------}

-- | How to color keywords.
keywordOpts :: [SGR]
keywordOpts = [SetColor Foreground Vivid Blue]

-- | How to color typenames.
typenameOpts :: [SGR]
typenameOpts = [SetColor Foreground Dull Green]

-- | Render to console using color highlighting.
renderANSI :: SimpleDocStream Annotation -> IO ()
renderANSI = \case
    SFail        -> return ()
    SEmpty       -> return ()
    SChar c x    -> do
      putStr $ c : []
      renderANSI x
    SText _l t x -> do
      putStr (T.unpack t)
      renderANSI x
    SLine i x    -> do
      putStr ('\n' : T.unpack (T.replicate i (T.singleton ' ')))
      renderANSI x
    SAnnPush Keyword x -> do
      setSGR keywordOpts
      renderANSI x
    SAnnPush TypeName x -> do
      setSGR typenameOpts
      renderANSI x
    SAnnPop x    -> do
      setSGR [Reset]
      renderANSI x

{---------------------------------------------
-----------Exported Functions-----------------
---------------------------------------------}

-- | Render a MyDoc as a String
docToString :: MyDoc -> String
docToString doc = renderString $ layoutPretty defaultLayoutOptions doc

-- | Print a MyDoc on the Terminal
docToTerminal :: MyDoc -> IO ()
docToTerminal doc = do
  putStrLn ""
  renderANSI $ layoutPretty defaultLayoutOptions doc
  putStrLn ""

-- | Prettyprint an expression as a string.
exprToMyDoc :: PrettyPrinterConfig -> Coq_expr -> MyDoc
exprToMyDoc ppConfig =   (flip runReader ppConfig)
                        . exprToDoc
                        . deBruijnToNamed
                        . either (error "Could not change coq program to DeBruijn") id
                        . coqToDeBruijn (program_skeleton (program ppConfig))

-- | Prettyprint all datatypes as a string.
datatypesToMyDoc :: PrettyPrinterConfig -> Coq_dts -> Coq_ctors -> MyDoc
datatypesToMyDoc ppConfig dts ctors = flip runReader ppConfig $ datatypesToDoc dts ctors

-- | Prettyprint all codatatypes as a string.
codatatypesToMyDoc :: PrettyPrinterConfig -> Coq_cdts -> Coq_dtors -> MyDoc
codatatypesToMyDoc ppConfig cdts dtors = flip runReader ppConfig $ codatatypesToDoc cdts dtors

-- | Prettyprint a program as a string.
progToMyDoc :: PrettyPrinterConfig -> Coq_program -> MyDoc
progToMyDoc ppConfig = (flip runReader ppConfig) . programToDoc
