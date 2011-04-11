import System.Environment (getArgs)
import System.Exit (exitFailure)

import AbsJavalette
import LexJavalette
import ParJavalette
import ErrM

import TypeChecker
import CodeGeneration

-- driver

check :: String -> IO ()
check s = case pProgram (myLexer s) of
            Bad err  -> do putStrLn "SYNTAX ERROR"
                           putStrLn err
                           exitFailure 
            Ok  tree -> case typecheck tree of
                          Bad err -> do putStrLn "TYPE ERROR"
                                        putStrLn err
                                        putStrLn (show tree)
                                        exitFailure 
                          Ok e    -> putStrLn $ "OK\n\n" ++ (show e)
--                          Ok p    -> testGenCode p "Main"


main :: IO ()
main = do args <- getArgs
          case args of
            [file] -> readFile file >>= check
            _      -> do putStrLn "Usage: lab2 <SourceFile>"
                         exitFailure
