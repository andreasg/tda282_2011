import System.Environment (getArgs)
import System.Exit (exitFailure)

import AbsJavalette
import LexJavalette
import ParJavalette
import ErrM

import TypeChecker
import CodeGeneration

-- driver

check :: String -> String -> IO ()
check n s = case pProgram (myLexer s) of
             Bad err  -> do putStrLn "SYNTAX ERROR"
                            putStrLn err
                            exitFailure 
             Ok  tree -> case typecheck tree of
                           Bad err -> do putStrLn "TYPE ERROR"
                                         putStrLn err
                                         exitFailure 
                           Ok p    -> putStrLn (genCode p (takeWhile (/='.') n))


main :: IO ()
main = do args <- getArgs
          case args of
            [file] -> readFile file >>= check file
            _      -> do putStrLn "Usage: Jl <SourceFile>"
                         exitFailure
