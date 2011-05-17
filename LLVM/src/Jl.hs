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
compile :: String -> Bool -> String -> IO ()
compile n compile s = case pProgram (myLexer s) of
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
                                                   if compile 
                                                     then do runCommand $ "llvm-as " ++ (dir ++ "/" ++ name++".ll") ++ " && " ++ "llvm-ld " ++ name++".bc" ++ " lib/runtime.bc"
                                                             return ()
                                                     else return ()


ePutStrLn = hPutStrLn stderr
                                         

main :: IO ()
main = do args <- getArgs
          case args of
            [file]     -> readFile file >>= compile file True
            [cmd,file] -> case cmd of
                            "-t" -> readFile file >>= check
                            "-nc" -> readFile file >>= compile file False
                            "--no-compile" -> readFile file >>= compile file False
                            _    -> putStrLn "invalid option"
            _      -> do putStrLn $ "Usage: ./jlc <SourceFile> to compile sourcefile to binary.\n" ++
                                    "       ./jlc -t <SourceFile> to print a type-annotated ABS to stdout.\n" ++
                                    "       ./jlc -nc <SourceFile> to only output LLVM assembly file, without compiling\n" ++
                                    "       ./jlc --no-compile <SourceFile> to only output LLVM assembly file, without compiling\n"

                         exitFailure
