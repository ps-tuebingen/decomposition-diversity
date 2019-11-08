{-# LANGUAGE OverloadedStrings, DeriveGeneric #-}
module JsonServer (startServer) where

import Network.JsonRpc.Server
import qualified Network.WebSockets as WS

import Data.Maybe (fromMaybe)
import Control.Monad.Except (throwError)
import Data.Text hiding (length)
import Data.Default

import AST
import Names
import JSON.GenericDerive ()
import ProgramDef
import Prettyprinter.Definitions
import Prettyprinter.Render
import Eval
import Parser.Combined
import XStructorize

startServer :: IO ()
startServer = do
  putStrLn "Starting up..."
  WS.runServer address port application
  where
    port = 9999
    address = "0.0.0.0"

application :: WS.ServerApp
application pending = do
  putStrLn "Got pending"
  conn <- WS.acceptRequest pending
  putStrLn "Found connection"
  loop conn
   where
    loop conn = do
        request <- WS.receiveData conn
        putStr "Request:\t"
        if length (show request) > 10000
           then putStrLn "Request too long"
           else print request
        response <- call methods request
        putStr "Response:\t"
        print response
        WS.sendTextData conn $ fromMaybe "" response
        loop conn

methods :: [Method IO]
methods = [ parseExprMethod
          , onestepEval
          , defuncProgram
          , refuncProgram
          , prettyPrintProgram
          , prettyPrintExpression
          , parseProgramFun
          ]

parseExprMethod :: Method IO
parseExprMethod = toMethod "parseExpr" f (Required "Coq_program" :+: Required "expr" :+: ())
    where f :: Coq_program -> String -> RpcResult IO Coq_expr
          f prog s = case parseExpression (program_skeleton prog) s of
                        Left e -> throwError $ rpcError (-32001) (pack e)
                        Right e -> return $ e

onestepEval :: Method IO
onestepEval = toMethod "onestepEval" f (Required "Coq_program" :+: Required "expr" :+: ())
    where f :: Coq_program -> Coq_expr -> RpcResult IO Coq_expr
          f prog expr = case one_step_eval prog expr of
                          Just e -> return e
                          Nothing -> throwError $ rpcError (-32002) "OnestepEval failed:\nEither the input was a value or there is a bug"

refuncProgram :: Method IO
refuncProgram = toMethod "destructorize" f (Required "Coq_program" :+: Required "typename" :+: ())
    where f :: Coq_program -> TypeName -> RpcResult IO Coq_program
          f prog tn = return $ dtorize tn prog


defuncProgram :: Method IO
defuncProgram = toMethod "constructorize" f (Required "Coq_program" :+: Required "typename" :+: ())
    where f :: Coq_program -> TypeName -> RpcResult IO Coq_program
          f prog tn = return $ ctorize tn prog

(...) :: (a -> b) -> (c -> d -> a) -> c -> d -> b
(...) = (.) . (.)
infixr 9 ...

prettyPrintProgram :: Method IO
prettyPrintProgram = toMethod "prettyPrintProgram" f (Required "Coq_program" :+: Optional "config" def :+: ())
    where f :: Coq_program -> PrettyPrinterConfig -> RpcResult IO String
          f = return ... (flip progToString)
          progToString :: PrettyPrinterConfig -> Coq_program -> String
          progToString conf prog = docToString (progToMyDoc conf prog)

prettyPrintExpression :: Method IO
prettyPrintExpression = toMethod "prettyPrintExpression" f (Required "expression" :+: Optional "config" def :+: ())
    where f :: Coq_expr -> PrettyPrinterConfig -> RpcResult IO String
          f = return ... (flip exprToString)
          exprToString :: PrettyPrinterConfig -> Coq_expr -> String
          exprToString conf expr = docToString (exprToMyDoc conf expr)

parseProgramFun :: Method IO
parseProgramFun = toMethod "parseProgram" f (Required "string" :+: ())
    where f :: String -> RpcResult IO Coq_program
          f s = case parseProgram s of
                  Left err -> throwError $ rpcError (-32004) $ pack err
                  Right p -> return p

