import System.Environment (getArgs)
import System.Exit (exitFailure)

import System.FilePath
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

check :: String -> String -> IO ()
check n s = case pProgram (myLexer s) of
             Bad err  -> do ePutStrLn "ERROR"
                            putStrLn err
                            exitFailure 
             Ok  tree -> case typecheck tree of
                           Bad err -> do ePutStrLn "ERROR"
                                         putStrLn err
                                         exitFailure 
                           Ok p    -> do ePutStrLn "OK"
                                         let name = (dropExtensions . takeFileName) n
                                         let dir  = takeDirectory n
                                         let code = genCode p name
                                         writeFile (dir ++ "/" ++ name++".j") code
                                         runCommand $ "java -jar jasmin.jar -d " ++ dir ++ " " ++ (dir++"/"++name++".j")
                                         return ()
  where ePutStrLn = hPutStrLn stderr
                                         

--putStrLn (genCode p ((dropExtensions . takeFileName) n))


main :: IO ()
main = do args <- getArgs
          case args of
            [file] -> readFile file >>= check file
            _      -> do putStrLn "Usage: Jl <SourceFile>"
                         exitFailure
