module Main where

import JsonServer (startServer)
import Repl (repl)
import System.Environment (getArgs)

main :: IO ()
main = getArgs >>= command

command :: [String] -> IO ()
command ["--json"] = startServer
command _          = repl
