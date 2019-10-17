{-# LANGUAGE LambdaCase #-}
module Prettyprinter.Render
  (
    datatypesToString,
    datatypesToStringANSI,
    codatatypesToString,
    codatatypesToStringANSI,
    exprToString,
    exprToStringANSI,
    progToString,
    progToStringANSI,
    docToString,
    docToTerminal
  ) where

import System.Console.ANSI
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String
import Control.Monad.Reader

import ProgramDef
import Skeleton
import AST
import HaskellAST
import Renamer.DeBruijnToNamed
import Prettyprinter.PrettyprinterDefs
import Prettyprinter.PrettyprintExprs
import Prettyprinter.PrettyprintDeclarations

{--------------------------------------------
----Custom Backend for Console---------------
--------------------------------------------}

-- | How to color keywords.
keywordOpts :: [SGR]
keywordOpts = [SetColor Foreground Vivid Blue]

-- | How to color typenames.
typenameOpts :: [SGR]
typenameOpts = [SetColor Foreground Dull Green]

-- | How to color debug information.
debugOpts :: [SGR]
debugOpts = [SetColor Foreground Vivid Red]

-- | How to color comments.
commentOpts :: [SGR]
commentOpts = [Reset] --no highlighting

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
    SAnnPush Comment x -> do
      setSGR commentOpts
      renderANSI x
    SAnnPush TypeName x -> do
      setSGR typenameOpts
      renderANSI x
    SAnnPush Debug x -> do
      setSGR debugOpts
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
exprToString :: PrettyPrinterConfig -> Coq_expr -> String
exprToString ppConfig = docToString . (flip runReader ppConfig) . exprToDoc . exprDB2exprNamed . coqExpr2exprDB (program_skeleton (program ppConfig))

-- | Prettyprint an expression and print it on console. Keywords are color highlighted.
exprToStringANSI :: PrettyPrinterConfig -> Coq_expr -> IO ()
exprToStringANSI ppConfig = docToTerminal . (flip runReader ppConfig) . exprToDoc . exprDB2exprNamed . coqExpr2exprDB (program_skeleton (program ppConfig))

-- | Prettyprint all datatypes as a string.
datatypesToString :: PrettyPrinterConfig -> Coq_dts -> Coq_ctors -> String
datatypesToString ppConfig dts ctors = docToString ((flip runReader ppConfig) (datatypesToDoc dts ctors))

-- | Prettyprint all datatypes and print them on the console. Keywords are color highlighted.
datatypesToStringANSI :: PrettyPrinterConfig -> Coq_dts -> Coq_ctors -> IO ()
datatypesToStringANSI ppConfig dts ctors = docToTerminal ((flip runReader ppConfig) (datatypesToDoc dts ctors))

-- | Prettyprint all codatatypes as a string.
codatatypesToString :: PrettyPrinterConfig -> Coq_cdts -> Coq_dtors -> String
codatatypesToString ppConfig cdts dtors = docToString ((flip runReader ppConfig) (codatatypesToDoc cdts dtors))

-- | Prettyprint all codatatypes and print them on the console. Keywords are color highlighted.
codatatypesToStringANSI :: PrettyPrinterConfig -> Coq_cdts -> Coq_dtors -> IO ()
codatatypesToStringANSI ppConfig cdts dtors = docToTerminal ((flip runReader ppConfig) (codatatypesToDoc cdts dtors))

-- | Prettyprint a program as a string.
progToString :: PrettyPrinterConfig -> Coq_program -> String
progToString ppConfig = docToString . (flip runReader ppConfig) . programToDoc

-- | Prettyprint a program on the console, keywords are color highlighted.
progToStringANSI :: PrettyPrinterConfig -> Coq_program -> IO ()
progToStringANSI ppConfig = docToTerminal . (flip runReader ppConfig) . programToDoc
