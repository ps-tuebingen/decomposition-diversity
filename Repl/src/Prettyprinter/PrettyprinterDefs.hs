module Prettyprinter.PrettyprinterDefs where

import ProgramDef

import Data.Default
import Data.Text.Prettyprint.Doc
import Control.Monad.Reader

data Locality = Local | Global
  deriving (Eq)

instance Show Locality where
  show Local = "local "
  show Global = ""

data Annotation =
    Keyword
  | Comment
  | TypeName
  | Debug

type MyDoc = Doc Annotation

data PrettyPrinterConfig = PrettyPrinterConfig {
    program :: Coq_program
  , printLocalFuns :: Bool      -- ^ Whether to print local cfuns / gfuns
  , printQualifiedNames :: Bool -- ^ Whether names are printed as "true" or "Bool:true"
  , printNat :: Bool            -- ^ Whether values of type Nat are printed as numerals.
  , printDeBruijn :: Bool       -- ^ Specifies whether deBruijn Index of variables is printed additionally.
  }

instance Default PrettyPrinterConfig where
  def = PrettyPrinterConfig {
    program = emptyProgram,
    printLocalFuns = True,
    printQualifiedNames = False,
    printNat = True,
    printDeBruijn = False
    }
  


type PrettyPrinter = Reader PrettyPrinterConfig MyDoc

{---------------------------------------------
-----------General purpose pp functions-------
---------------------------------------------}

-- | Prettyprint a string and annotate it as a typename.
debuginfo :: String -> MyDoc
debuginfo = annotate Debug . pretty

-- | Prettyprint a string and annotate it as a typename.
typename :: String -> MyDoc
typename = annotate TypeName . pretty

-- | Prettyprint a string and annotate it as a keyword.
keyword :: String -> MyDoc
keyword = annotate Keyword . pretty

-- | Prettyprint a string and annotate it as a comment.
comment :: String -> MyDoc
comment = annotate Comment . pretty

runPrettyprinter :: PrettyPrinter -> MyDoc
runPrettyprinter pp = runReader pp def
