module CodeGeneration where

import AbsJavalette
import PrintJavalette
import ErrM
import Debug.Trace
import Data.List (nubBy)
import Control.Monad.State
import TypeChecker

--------------------------------------------------------------------------------
-- Types and Data
--------------------------------------------------------------------------------
type Result a = StateT Scope Err a
data Scope = Scope { stackDepth    :: Int
                   , maxStackDepth :: Int
                   , vars          :: [(Ident, Int)]
                   , label_count   :: Int
                   , label         :: Int 
                   , code          :: [String]
                   , className     :: String }
           deriving Show


-- |Create a new scope
newScope :: Int -> String -> Scope
newScope lbl name = Scope 0 0 [] 0 lbl [] name


-- instructions
iload  n = "iload_" ++ (show n)
dload  n = "dload_" ++ (show n)
bipush n = "bipush " ++ (show n)
ldc_w  n = "ldc_w "  ++ (show n)


-- |Get the numeric id for an identifier
lookupId :: Ident -> Result Int
lookupId id = do s <- get
                 case lookup id (vars s) of
                   Just i -> return i
                   Nothing -> fail "lookupId :: Ident not found in scope"
  

-- |Add code to the outmost scope
putCode :: [String] -> Result ()
putCode ss = modify (\s -> s {code = (code s ++ ss)})


-- |Modify the stack-depth for the current scope
incStack :: Int -> Result ()
incStack n = modify (\s -> 
                         s { maxStackDepth = max (maxStackDepth s) (maxStackDepth s + n)
                           , stackDepth    = (stackDepth s) + n } )

typeToChar :: Type -> Char
typeToChar t = case t of
                 Int  -> 'I'
                 Doub -> 'D'
                 Void -> 'V'
exprToChar :: Expr -> Char
exprToChar (TExp t _) = typeToChar t


-- |Generate code for an expression
exprCode :: Expr -> Result ()
exprCode (TExp t e) = 
 case e of
  EVar id      -> do i <- lookupId id -- bug here?
                     case t of
                       Int  -> putCode [iload i] >> incStack 1
                       Doub -> putCode [dload i]
  ELitInt i    -> putCode [bipush i] >> incStack 1
  ELitDoub d   -> putCode [ldc_w d]  >> incStack 1
  ELitTrue     -> putCode [bipush 1] >> incStack 1
  ELitFalse    -> putCode [bipush 0] >> incStack 1
  EApp (Ident id) es   -> 
      do mapM_ exprCode es
         s <- get
         putCode ["invokestatic " ++ className s ++ "/" ++ id ++
                 "(" ++ map exprToChar es ++ ")" ++ [typeToChar t]] >> if t == Void
                                                                        then incStack 0
                                                                        else incStack 1
  EString s    -> putCode ["ldc_w "++s]  >> incStack 1
  Neg exp      -> fail "exprCode:: Neg Expr: not implemented yet"
  Not exp      -> fail "exprCode:: Not Expr: not implemented yet"
  EMul e0 o e1 -> exprCode e0 >> exprCode e1 >>
                  case t of 
                    Int  -> putCode ["imul"] >> incStack 1
                    Doub -> putCode ["dmul"] >> incStack 1
  EAdd e0 o e1 -> exprCode e0 >> exprCode e1 >> 
                  case t of 
                    Int  -> putCode["iadd"] >> incStack (-1)
                    Doub -> putCode["dadd"] >> incStack (-1)
  ERel e0 o e1 -> fail "exprCode:: ERel Expr Op Expr: not implemented yet"
  EAnd e0 e1   -> exprCode e0 >> exprCode e1 >> putCode ["and"] >> incStack (-1)
  EOr  e0 e1   -> fail "exprCode:: EOr Expr Expr: not implemented yet"


--------------------------------------------------------------------------------
-- Test Functions
--------------------------------------------------------------------------------
testExpr :: [Expr] -> IO ()
testExpr es = case runStateT (mapM_ exprCode es) (newScope 0 "ClassName") of
                  Ok c -> putStrLn $ (unlines (code (snd c)) ++ "maxStackDepth = " ++ 
                                      (show ( maxStackDepth (snd c))))
                  _    -> putStrLn "testExpr fail"



-- Test xpression
eAddTest = [TExp Int (EAdd (TExp Int (ELitInt 10)) Plus (TExp Int (ELitInt 20)))]

eAppTest = [TExp Int (EApp (Ident "f") [TExp Int (ELitInt 10)
                                       ,TExp Doub (ELitDoub 2.0)
                                       ])]