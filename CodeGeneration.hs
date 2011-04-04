module CodeGeneration where

-- BNF Converter imports
import AbsJavalette
import AbsJavalette
import PrintJavalette
import ErrM

import Debug.Trace
import Data.List (nubBy)
import Control.Monad.State


stmtCode  = undefined


type Jasmin = [Instruction]

--type Function =  [Instruciton]

data Instruction = Store Int | 
                   Load  Int |
                   Return    


type Result a = State Jasmine a


--data VarMap = Data.map Ident (Int, Type)


putCode :: [Instruction] -> Result ()
putCode is = get >>= (\x -> put (x++is)) 



---get >>= (\x -> put (is++x))

--(put (++) is)



stmtCode :: Stmt -> Result ()
stmtCode (Decl typ (Init id expr : xs)) = do
  lbl <- getLabel
  putCode [exprCode expr, Store lbl]
  incPtr (-1)
stmtCode (Ret expr)       = do
  putCode [exprCode expr, Return]
  incPtr (-1)
stmtCode _ = undefined


exprCode :: Expr -> Result ()
exprCode (ELitInt i)       = 
exprCode (EVar (Ident id)) = 
exprCode (EAdd e0 Plus e1) = 
exprCode _           = undefined 

{-
exprCode :: Expr -> Result 
exprCode (EVar i)      = "iload_"   ++ show(getVarNum i)
exprCode ELitInt i     = "bipush " ++ show i
exprCode EAdd e0 Minus e1 = putCode [IAdd 
exprCode EAdd e0 Plus  e1 = 
exprCode e = undefined
-}