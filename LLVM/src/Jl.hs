import System.Environment (getArgs)
import System.Exit (exitFailure)

import System.FilePath
import System.Directory
import System.IO
import System.Process

import AbsJavalette
import LexJavalette
import ParJavalette
import ErrM

import Debug.Trace

import TypeChecker
import CodeGeneration

-- driver

-- |just typecheck and print the type-annotated ABS
check :: String -> IO ()
check  s =  putStrLn "Running typechecker only.\n\n" >>
            case pProgram (myLexer s) of
               Bad err  -> do putStrLn "ERROR"
                              putStrLn err
                              exitFailure 
               Ok  tree -> case typecheck tree of
                            Bad err -> do putStrLn "ERROR"
                                          putStrLn err
                                          exitFailure 
                            Ok p    -> do putStrLn "OK"
                                          putStrLn (show p)

-- | Compile the file
compile :: String -> String -> IO ()
compile n s = case pProgram (myLexer s) of
               Bad err  -> do ePutStrLn "ERROR"
                              putStrLn err
                              exitFailure 
               Ok  tree -> case typecheck tree of
                            Bad err -> do ePutStrLn "ERROR"
                                          putStrLn err
                                          exitFailure 
                            Ok p    -> do ePutStrLn "OK"
                                          let name = (dropExtensions . takeFileName) n
                                          let dir  = case takeDirectory n of
                                                      "" -> "."
                                                      d  -> d
                                          let code = genCode p
                                          writeFile (dir ++ "/" ++ name++".ll") code
                                          return ()


ePutStrLn = hPutStrLn stderr
                                         

main :: IO ()
main = do args <- getArgs
          case args of
            [file]     -> readFile file >>= compile file
            [cmd,file] -> case cmd of
                            "-t" -> readFile file >>= check
                            _    -> putStrLn "invalid option"
            _      -> do putStrLn $ "Usage: Jl <SourceFile>\n" ++
                                    "or     Jl -t <SourceFile> for a\n" ++
                                    "type-annotated ABS."
                         exitFailure
