
module Main where

import System.Exit (exitSuccess)
import System.Console.Repline
import System.Console.Haskeline
import System.Directory
import Control.Monad (filterM,when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.State.Strict
import Control.Monad.Except (lift)
import Data.List (isPrefixOf, isSuffixOf)
import Data.Default
import           Data.Maybe                     ( fromMaybe )
import Text.Read (readMaybe)
import System.IO.Error(tryIOError)
import Control.Monad.Trans

import TypecheckProgram
import Names
import AST
import ProgramDef
import Skeleton
import Prettyprinter.Definitions
import Prettyprinter.Render
import Eval
import LiftComatch
import InlineMatch
import InlineOrderCfuns
import CtorizeIII
import LiftMatch
import InlineComatch
import InlineOrderGfuns
import DtorizeIII
import Parser.Combined (parseExpression, parseProgram)

--------------------------------------------------------------------------------
-- The Repl Monad
--------------------------------------------------------------------------------

data CommandMode
  = NormalMode
  | MultilineExprMode String
  | MultilineDeclarationMode String

data ReplState = ReplState
  {
    currentProgram      :: Coq_program
  , commandMode         :: CommandMode
  , lastLoadedFile      :: Maybe String
  , prettyPrinterConfig :: PrettyPrinterConfig
  }

type Repl = HaskelineT (StateT ReplState IO)
type InnerRepl = StateT ReplState IO

--------------------------------------------------------------------------------
-- Helper functions for the Repl Monad
--------------------------------------------------------------------------------

extractFromReplState :: (Monad m, MonadTrans t) => (ReplState -> a) -> t (StateT ReplState m) a
extractFromReplState = lift . gets

modifyReplState :: (ReplState -> ReplState) -> Repl ()
modifyReplState f = do replState <- lift get
                       lift $ put $ f replState

safeRead :: FilePath -> Repl (Maybe String)
safeRead file = liftIO $ do
  res <- tryIOError (readFile file)
  case res of
    (Left _) -> return Nothing
    (Right s) -> return $ Just s

putReplStrLn :: String -> Repl ()
putReplStrLn s = liftIO (putStrLn s)

getCommandMode :: Repl CommandMode
getCommandMode = extractFromReplState commandMode

getPrettyPrinterConfig :: Repl PrettyPrinterConfig
getPrettyPrinterConfig = do
  myprogram <- extractFromReplState currentProgram
  ppConfig <- extractFromReplState prettyPrinterConfig
  return (ppConfig { program = myprogram })

-- | Wrap a Repl () action which should only be executed when in normal mode.
-- This handles the case when a ":<cmd>" is entered while in multiline mode.
execIfInNormalMode :: Repl () -> Repl ()
execIfInNormalMode cmd = do
  mode <- getCommandMode
  case mode of
    NormalMode -> cmd
    _ -> do
      putReplStrLn "Aborted multiline input."
      modifyReplState (\st -> st { commandMode = NormalMode })

getDatatypes :: InnerRepl [TypeName]
getDatatypes = do
  program <- gets currentProgram
  case program of
    Coq_mkProgram sk _ _ _ _ _ ->
      case sk of
        Coq_mkSkeleton dts _ _ _ _ _ _ _ _-> return dts

getCodatatypes :: InnerRepl [TypeName]
getCodatatypes = do
  program <- gets currentProgram
  case program of
    Coq_mkProgram sk _ _ _ _ _ ->
      case sk of
        Coq_mkSkeleton _ _ cdts _ _ _ _ _ _-> return cdts

--------------------------------------------------------------------------------
-- Possible Commands
--------------------------------------------------------------------------------

options :: [(String, [String] -> Repl ())]
options = [
    ("help",            help)
  , ("quit",            quit)
  , ("showprogram",     showProgram)
  , ("constructorize",  constructorize)
  , ("destructorize",   destructorize)
  , ("transpose",       transpose)
  , ("load",            load)
  , ("reload",          reload)
  , ("declare",         declare)
  , ("step",            stepCmd)
  , ("set",             set)
  , ("unset",           unset)
  ]

--------------------------------------------------------------------------------
-- :help
-- 
-- Show Help
--------------------------------------------------------------------------------

help :: [String] -> Repl ()
help _ = putReplStrLn $
  "Commands available from the prompt: \n\n" ++
  "<expression>            evaluate the expression\n" ++
  ":help                   display this list of commands\n" ++
  ":quit                   exit the repl\n" ++
  ":showprogram            show all declarations\n" ++
  ":constructorize <x>     constructorize the current program\n" ++
  ":destructorize <x>      destructorize the current program\n" ++
  ":load <filename>        load program from file\n" ++
  ":reload                 reload last sucessfully loaded program\n" ++
  ":declare                add a declaration to the program\n" ++
  ":step <n> <expr>       evaluate n steps of expressions in context of the loaded program\n" ++
  "\n --- Pretty printing options ---\n" ++
  ":set / :unset [option]  enable / disable prettyprinting option\n" ++
  "Options:\n" ++
  " - printNat             print values of Nat as numerals\n" ++
  " - printDeBruijn        print variables with their deBruijn Index (Debug mode)\n" ++
  " - printQualifiedNames  print ctors/dtors with their qualified names\n"

--------------------------------------------------------------------------------
-- :quit
--
-- Exit the Program
--------------------------------------------------------------------------------

quit :: [String] -> Repl ()
quit _ = execIfInNormalMode $
  liftIO exitSuccess

--------------------------------------------------------------------------------
-- :showprogram
--
-- Shows the program in the current state
--------------------------------------------------------------------------------

showProgram :: [String] -> Repl ()
showProgram _ = execIfInNormalMode $ do
  prog <- extractFromReplState currentProgram
  ppConfig <- getPrettyPrinterConfig
  liftIO $ docToTerminal $ progToMyDoc (ppConfig {program = prog}) prog


--------------------------------------------------------------------------------
-- :constructorize <codatatype>
--
-- Constructorizes the given codata type
--------------------------------------------------------------------------------

constructorizeProg :: TypeName -> Coq_program -> Coq_program
constructorizeProg tn = inline_cfuns_to_program . reorder_cfuns . flip constructorize_program tn . flip lift_comatch_to_program tn

-- | Takes one argument and replaces the current Program by its constructorized version.
constructorize :: [String] -> Repl ()
constructorize [] = execIfInNormalMode $ putReplStrLn "Constructorize needs at least one codatatype parameter"
constructorize (arg:_) = execIfInNormalMode $ do
  loadedProg <- extractFromReplState currentProgram
  let newProg = constructorizeProg arg loadedProg
  lift $ modify $ \replState -> (replState {currentProgram =  newProg})
  putReplStrLn "Successfully constructorized program!"

--------------------------------------------------------------------------------
-- :destructorize <codatatype>
--
-- Destructorizes the given data type
--------------------------------------------------------------------------------

destructorizeProg :: TypeName -> Coq_program -> Coq_program
destructorizeProg tn = inline_gfuns_to_program . reorder_gfuns . flip destructorize_program tn . flip lift_match_to_program tn

-- | Takes one argument and replaces the current Program by its constructorized version.
destructorize :: [String] -> Repl ()
destructorize [] = execIfInNormalMode $ putReplStrLn "Destructorize needs at least one datatype parameter"
destructorize (arg:_) = execIfInNormalMode $ do
  loadedProg <- extractFromReplState currentProgram
  let newProg = destructorizeProg arg loadedProg
  lift $ modify $ \replState -> (replState {currentProgram =  newProg})
  putReplStrLn "Successfully destructorized program!"

--------------------------------------------------------------------------------
-- :destructorize <codatatype>
--
-- Destructorizes the given data type
--------------------------------------------------------------------------------

transpose :: [String] -> Repl ()
transpose [] = execIfInNormalMode $ putReplStrLn "Transposition needs at least one datatype parameter"
transpose (arg:_) = execIfInNormalMode $ do
  loadedProg <- extractFromReplState currentProgram
  dts <- lift getDatatypes
  cdts <- lift getCodatatypes
  case (arg `elem` dts, arg `elem` cdts) of
    (True, _) -> do
        let newProg = destructorizeProg arg loadedProg
        lift $ modify $ \replState -> (replState {currentProgram =  newProg})
        putReplStrLn "Successfully destructorized program!"
    (False, True) -> do
        let newProg = constructorizeProg arg loadedProg
        lift $ modify $ \replState -> (replState {currentProgram =  newProg})
        putReplStrLn "Successfully constructorized program!"
    _ -> putReplStrLn $ "Transposing program with type " ++ arg ++ " failed"

--------------------------------------------------------------------------------
-- :load <filename>
--
-- Load the file with the given name from disk.
-- Parses and typechecks the file.
--------------------------------------------------------------------------------

load :: [String] -> Repl ()
load [] = execIfInNormalMode $ putReplStrLn "Load needs a filename parameter"
load (filepath:_) = execIfInNormalMode $ do
  mprogstr <- safeRead filepath
  case mprogstr of
    Nothing -> putReplStrLn $ "File with name " ++ filepath ++ " does not exist."
    Just progstr ->
        case parseProgram progstr of
          Left err -> putReplStrLn $ "Failed at parsing the file:\n" ++ err
          Right parsedProg -> do
            let tc_errors = typecheckProgram parsedProg
            case tc_errors of
              (([],[]),[]) -> do
                lift $ modify $ \replState -> replState {currentProgram = parsedProg, lastLoadedFile = Just filepath}
                putReplStrLn "Successfully loaded program"
              ((ferrs, gfunerrs), cfunerrs) -> do
                if null ferrs then return () else do
                  putReplStrLn $ "Could not typecheck the following functions: "
                  mapM_ putReplStrLn ferrs
                if null gfunerrs then return () else do
                  putReplStrLn $ "Could not typecheck the following generator functions: "
                  mapM_ putReplStrLn gfunerrs
                if null cfunerrs then return () else do
                  putReplStrLn $ "Could not typecheck the following consumer functions: "
                  mapM_ putReplStrLn cfunerrs

--------------------------------------------------------------------------------
-- :reload
--
-- Takes filename of the last successfully loaded program and reloads that program
-- from the filesystem.
--------------------------------------------------------------------------------

reload :: [String] -> Repl ()
reload _ = execIfInNormalMode $ do
  lastLoadedFile <- extractFromReplState lastLoadedFile
  case lastLoadedFile of
    Nothing -> putReplStrLn "No file has been successfully loaded before"
    Just filepath -> do
      mprogstr <- safeRead filepath
      case mprogstr of
        Nothing -> putReplStrLn $ "File with name " ++ filepath ++ " does not exist."
        Just progstr ->
          case parseProgram progstr of
            Left err -> putReplStrLn $ "Failed at parsing the file:\n" ++ err
            Right p -> do
              lift $ modify $ \replState -> replState {currentProgram = p}
              putReplStrLn "Successfully reloaded program"

--------------------------------------------------------------------------------
-- :declare
--
-- Add a declaration to the program. Starts multiline declaration mode.
--------------------------------------------------------------------------------

declare :: [String] -> Repl ()
declare _ = execIfInNormalMode $
  modifyReplState (\st -> st { commandMode = MultilineDeclarationMode "" })

--------------------------------------------------------------------------------
-- :step
--
-- Expects two arguments, a max number of steps and an expression to execute.
--------------------------------------------------------------------------------

-- | Parse the arguments. If successful, pass result to "step" function.
stepCmd :: [String] -> Repl ()
stepCmd [] = putReplStrLn ":step expects two arguments."
stepCmd (s:ss) = do
  program <- extractFromReplState currentProgram
  case readMaybe s of
    Nothing -> putReplStrLn "Could not parse first argument of :step as integer"
    Just n  -> case parseExpression (program_skeleton program) (concat ss) of
      Left err -> putReplStrLn err
      Right e -> step n e

step :: Int -> Coq_expr -> Repl ()
step n e = do
  steps <- computeSteps n e
  printSteps (reverse steps)

-- | Try to evaluate an expression to normal form, returning all intermediate steps.
-- Additional parameter is used to indicate the maximal number of steps.
computeSteps :: Int -> Coq_expr -> Repl [Coq_expr]
computeSteps n e = do
  program <- extractFromReplState currentProgram
  let go n' e acc
        | n' <= 0   = return acc
        | value_b e = return (e:acc)
        | otherwise = case one_step_eval program e of
                        Nothing -> return (e:acc)
                        Just e' -> go (n' - 1) e' (e:acc)
  go n e []

-- | Print the list of expressions to console.
printSteps :: [Coq_expr] -> Repl ()
printSteps exprs = do
  ppConfig <- getPrettyPrinterConfig
  let printStep :: (Int, Coq_expr) -> Repl ()
      printStep (n,e) = do
        putReplStrLn $ "STEP " ++ show n
        liftIO $ docToTerminal $ exprToMyDoc ppConfig e
  let numberedExprs = zip [1..] exprs
  sequence_ (printStep <$> numberedExprs)

--------------------------------------------------------------------------------
--  :set :unset
--
-- Set and unset options.
--------------------------------------------------------------------------------

setOptions :: [String]
setOptions =  [ "printNat"
              , "printDeBruijn"
              , "printQualifiedNames"
              ]

setPrintNat :: Bool -> ReplState -> ReplState
setPrintNat b rs@ReplState { prettyPrinterConfig = ppConfig} = rs {prettyPrinterConfig = (ppConfig { printNat = b })}

setPrintDeBruijn :: Bool -> ReplState -> ReplState
setPrintDeBruijn b rs@ReplState { prettyPrinterConfig = ppConfig} = rs {prettyPrinterConfig = (ppConfig { printDeBruijn = b })}

setPrintQualifiedNames :: Bool -> ReplState -> ReplState
setPrintQualifiedNames b rs@ReplState { prettyPrinterConfig = ppConfig} = rs {prettyPrinterConfig = (ppConfig { printQualifiedNames = b })}

set, unset :: [String] -> Repl ()
set = xSet True
unset = xSet False

xSet :: Bool -> [String] -> Repl ()
xSet b args = do
  when ("printNat" `elem` args) $ lift $ modify (setPrintNat b)
  when ("printDeBruijn" `elem` args) $ lift $ modify (setPrintDeBruijn b)
  when ("printQualifiedNames" `elem` args) $ lift $ modify (setPrintQualifiedNames b)


--------------------------------------------------------------------------------
-- Command
--
-- Input on the repl not preceded by a colon is passed on to cmd.
-- cmd tries to parse the string as an expression and evaluates it with
-- the currently loaded program.
--------------------------------------------------------------------------------

-- | Dispatch based on current mode of the repl.
cmd :: String -> Repl ()
cmd input = do
  mode <- getCommandMode
  case mode of
    NormalMode -> cmdNormalMode input
    MultilineExprMode akk -> cmdMultilineExprMode akk input
    MultilineDeclarationMode akk -> cmdMultilineDeclMode akk input

-- | If in normal mode, we try to parse an Expression.
-- If this fails, we switch to multiline expression input mode.
cmdNormalMode :: String -> Repl ()
cmdNormalMode input = do
  program <- extractFromReplState currentProgram
  let tryParse = parseExpression (program_skeleton program) input
  case tryParse of
    Left _ -> modifyReplState (\st -> st { commandMode = MultilineExprMode input })
    Right expr -> evalExpr expr

-- | Decide whether multiline input is finished, or whether input should be appended to
-- accumulated multiline input.
cmdMultilineExprMode :: String -> String -> Repl ()
cmdMultilineExprMode akk ";" = do
  modifyReplState (\st -> st { commandMode = NormalMode })
  evalMultilineExpr akk
cmdMultilineExprMode akk input =
  modifyReplState (\st -> st { commandMode = MultilineExprMode (akk ++ "\n" ++ input) })

-- | Process the accumulated and finished multiline expression input.
evalMultilineExpr :: String -> Repl ()
evalMultilineExpr multilineExpr = do
  program <- extractFromReplState currentProgram
  let tryParse = parseExpression (program_skeleton program) multilineExpr
  case tryParse of
    Left err -> do
      putReplStrLn "Error while parsing multiline expression:"
      putReplStrLn err
      modifyReplState (\st -> st { commandMode = NormalMode })
    Right expr -> evalExpr expr

-- | Decide whether multiline input is finished, or whether input should be appended to
-- accumulated multiline input.
cmdMultilineDeclMode :: String -> String -> Repl ()
cmdMultilineDeclMode akk ";" = do
  modifyReplState (\st -> st { commandMode = NormalMode })
  evalMultilineDecl akk
cmdMultilineDeclMode akk input  =
  modifyReplState (\st -> st { commandMode = MultilineDeclarationMode (akk ++ "\n" ++ input) })

-- | Process the accumulated and finished multiline declaration input.
evalMultilineDecl :: String -> Repl ()
evalMultilineDecl = putReplStrLn

evalFully :: Coq_program -> Coq_expr -> Maybe Coq_expr
evalFully p e
  | value_b e = Just e
  | otherwise = case one_step_eval p e of
                  Nothing -> Nothing
                  Just e' -> evalFully p e'

evalExpr :: Coq_expr -> Repl ()
evalExpr e = do
  program <- extractFromReplState currentProgram
  ppConfig <- getPrettyPrinterConfig
  let val = evalFully program e
  putReplStrLn"Parsed input as:"
  liftIO $ docToTerminal $ exprToMyDoc ppConfig e
  putReplStrLn "Evaluates to:"
  liftIO $ case val of
    Nothing -> putStrLn "evalFully failed, returning Nothing"
    Just val' -> docToTerminal $ exprToMyDoc ppConfig val'

--------------------------------------------------------------------------------
-- Tab Completion
--------------------------------------------------------------------------------

completionlist :: [String]
completionlist = (':':) . fst <$> options

completer :: CompleterStyle InnerRepl
completer = Prefix cmdCompleter prefixCompleters
  where
    prefixCompleters =
      [
        (":destructorize", destructorizeCompleter)
      , (":constructorize", constructorizeCompleter)
      , (":transpose", transposeCompleter)
      , (":set", setCompleter)
      , (":unset", setCompleter)
      , (":load", fileCompleter)
      ]

mkWordCompleter :: Monad m =>  (String -> m [Completion]) -> CompletionFunc m
mkWordCompleter = completeWord (Just '\\') " \t()[]"

-- | Just completes commands. e.g. ":showprogram", ":load" etc.
cmdCompleter :: Monad m => CompletionFunc m
cmdCompleter = mkWordCompleter (_simpleComplete f)
  where
    f n = return $ filter (isPrefixOf n) completionlist
    _simpleComplete f word = map simpleCompletion <$> f word

-- | Completes ":destructorize" commands with available datatypes.
destructorizeCompleter :: CompletionFunc InnerRepl
destructorizeCompleter = mkWordCompleter getDestructorizeCompletions
  where
    getDestructorizeCompletions s = do
      dts <- getDatatypes
      let filtered = filter (isPrefixOf s) dts
      return $ fmap simpleCompletion filtered

-- | Completes ":constructorize" commands with available codatatypes.
constructorizeCompleter :: CompletionFunc InnerRepl
constructorizeCompleter = mkWordCompleter getConstructorizeCompletions
  where
    getConstructorizeCompletions s = do
      cdts <- getCodatatypes
      let filtered = filter (isPrefixOf s) cdts
      return $ fmap simpleCompletion filtered

-- | Completes ":constructorize" commands with available codatatypes.
transposeCompleter :: CompletionFunc InnerRepl
transposeCompleter = mkWordCompleter getTransposeCompletions
  where
    getTransposeCompletions s = do
      dts <- getDatatypes
      cdts <- getCodatatypes
      let filtered = filter (isPrefixOf s) (dts ++ cdts)
      return $ fmap simpleCompletion filtered

-- | Completes ":set" and ":unset" commands with available options.
setCompleter :: CompletionFunc InnerRepl
setCompleter = mkWordCompleter getSetCompletions
  where
    getSetCompletions s = return $ simpleCompletion <$> filter (isPrefixOf s) setOptions

--------------------------------------------------------------------------------
-- Setting up the Repl
--------------------------------------------------------------------------------

startState :: ReplState
startState = ReplState
  {
    currentProgram = emptyProgram
  , commandMode = NormalMode
  , lastLoadedFile = Nothing
  , prettyPrinterConfig = def
  }

splashScreen :: Repl ()
splashScreen = putReplStrLn $ unlines
  [ "    ____                                             _ __  _           "
  , "   / __ \\___  _________  ____ ___  ____  ____  _____(_) /_(_)___  ____ "
  , "  / / / / _ \\/ ___/ __ \\/ __ `__ \\/ __ \\/ __ \\/ ___/ / __/ / __ \\/ __ \\"
  , " / /_/ /  __/ /__/ /_/ / / / / / / /_/ / /_/ (__  ) / /_/ / /_/ / / / /"
  , "/_____/\\___/\\___/\\____/_/ /_/ /_/ .___/\\____/____/_/\\__/_/\\____/_/ /_/ "
  , "    ____  _                    /_/ __                                  "
  , "   / __ \\(_)   _____  __________(_) /___  __                           "
  , "  / / / / / | / / _ \\/ ___/ ___/ / __/ / / /                           "
  , " / /_/ / /| |/ /  __/ /  (__  ) / /_/ /_/ /                            "
  , "/_____/_/ |___/\\___/_/  /____/_/\\__/\\__, /                             "
  , "                                   /____/                              "
  , ""
  , "Enter :help for a list of available commands."
  ]
prompt :: Repl String
prompt = do
  lastLoaded <- extractFromReplState lastLoadedFile
  mode <- getCommandMode
  let promptPrefix = fromMaybe "" lastLoaded
  case mode of
    NormalMode -> return $ promptPrefix ++ "> "
    MultilineExprMode _ -> return $ promptPrefix ++ ": "
    MultilineDeclarationMode _ -> return $ promptPrefix ++ ": "

repl :: IO ()
repl = evalStateT (evalRepl prompt cmd options (Just ':') completer splashScreen) startState

main :: IO ()
main = repl
