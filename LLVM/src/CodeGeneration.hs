module CodeGeneration where

import AbsJavalette
import PrintJavalette
import ErrM
import Debug.Trace
import Data.List (nubBy, init, last)
import Data.Maybe (fromJust)
import Control.Monad.State

import ReturnChecker

--------------------------------------------------------------------------------
-- Types and Data
--------------------------------------------------------------------------------
type Result a = State [a] a
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Statement Code Generations
--------------------------------------------------------------------------------
-- | Generate Jasmin code for a Javalette Statement
stmtCode :: Stmt -> Result ()
stmtCode stmt =
 case stmt of
  Empty                             -> undefined
  (BStmt (Block ss))                -> undefined
  Decl t is                         -> undefined
  Ass id e@(TExp t e')              -> undefined
  Incr id                           -> undefined
  Decr id                           -> undefined
  Ret e@(TExp t _)                  -> undefined
  VRet                              -> undefined
  Cond (TExp Bool ELitTrue) stmt    -> undefined
  Cond (TExp Bool ELitFalse) stmt   -> undefined
  Cond expr stmt                    -> undefined
  CondElse (TExp Bool ELitTrue) s _ -> undefined
  CondElse (TExp Bool ELitFalse) _ s-> undefined
  CondElse expr s0 s1               -> undefined
  While expr stmt                   -> undefined
  SExp e@(TExp t e')                -> undefined
  ArrAss id ds0 e@(TExp t _)        -> undefined
  For t' i0 i1 s                    -> undefined
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Expression Code Generation
--------------------------------------------------------------------------------
-- |Generate code for an expression
exprCode :: Expr -> Result ()
exprCode (TExp t e) =
 case e of
  EVar id      -> undefined
  ELitInt i    -> undefined
  ELitDoub d   -> undefined
  ELitTrue     -> undefined
  ELitFalse    -> undefined
  EApp (Ident "printString") [TExp _ (EString s)] -> undefined
  EApp (Ident "printInt") es    -> undefined
  EApp (Ident "printDouble") es -> undefined
  EApp (Ident "readInt")    _   -> undefined
  EApp (Ident "readDouble") _   -> undefined
  EApp (Ident id) es -> undefined
  EString s    -> undefined
  Neg exp      -> undefined
  Not exp      -> undefined
  EMul e0 o e1 -> undefined
  EAdd e0 o e1 -> undefined
  ERel e0@(TExp t' _) o e1 -> undefined
  EAnd e0 e1   -> undefined
  EOr  e0 e1   -> undefined
  EArr    t  [EDimen e] -> undefined
  EArr    t'  ds -> undefined
  EArrLen id   -> undefined
  EArrMDLen id ds -> undefined
  EArrIdx id [EDimen e] -> undefined
  EArrIdx id ds -> undefined

exprCode e = trace (show e) (return ())
--------------------------------------------------------------------------------