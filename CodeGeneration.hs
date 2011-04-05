module CodeGeneration where

-- BNF Converter imports
import AbsJavalette
import PrintJavalette
import ErrM

import Debug.Trace
import Data.List (nubBy)
import Control.Monad.State

type Jasmin = [Instruction]


---type Env 

data Instruction = Store Int     | 
                   Load  Int     |
                   Add           |
                   Sub           |
                   Push  Integer | 
                   Return
                   deriving Show

type Result a = State Jasmin a


putCode :: [Instruction] -> Result ()
putCode is = get >>= (\x -> put (x++is)) 


genCode :: [Instruction] -> Result String
genCode []     = return ""
genCode (i:is) = 
    case i of
      Store i -> genCode is >>= (\x -> return ("istore " ++ show i ++ "\n" ++ x))
      Load  i ->undefined
      Add     ->undefined
      Sub     ->undefined
      Push i  -> genCode is >>= (\x -> return ("ipush " ++ show i ++ "\n" ++ x))
      Return  -> do
             s <- genCode is
             return ("iret" ++ "\n" ++ s)



stmtCode :: Stmt -> Result ()
stmtCode (Decl typ (Init id expr : xs)) = do
  lbl <- getLabel id
  exprCode expr
  putCode [Store lbl]
--  incPtr (-1)
stmtCode (Ret expr)       = do
  exprCode expr
  putCode [Return]
--  incPtr (-1)
stmtCode s = undefined


exprCode :: Expr -> Result ()
exprCode (ELitInt i)       = putCode [Push i]
exprCode (EVar id) = do
  l <- getLabel id
  putCode [Load l]
exprCode (EAdd e0 Plus e1) = do
  exprCode e0
  exprCode e1
  putCode [Add]
--  incPtr (-1)
exprCode _           = undefined 


getLabel :: Ident -> Result Int
getLabel i = return 10


incPtr :: Integer -> Result ()
incPtr i = undefined