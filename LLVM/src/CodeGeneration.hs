module CodeGeneration (genCode) where


--------------------------------------------------------------------------------
-- Imports.
--------------------------------------------------------------------------------
import AbsJavalette
import PrintJavalette
import ErrM
import Debug.Trace
import Data.List (nubBy, init, last)
import Data.Maybe (fromJust)
import Control.Monad.State

import ReturnChecker
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Types and Data.
--------------------------------------------------------------------------------
type Result = State Env

-- | Environment used to keep track of all data during code-gen.
data Env = Env
  { nextRegister :: Int                -- next num for register/label gen
  , strings      :: [(Ident,String)]   -- global string literals
  , vars         :: [[(Ident,String)]] -- variables
  , funs         :: [(Ident,Type)]     -- function types
  , code         :: [String]
  }
emptyEnv :: Env
emptyEnv = Env 0 [] [] [] []
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- File header
--------------------------------------------------------------------------------
datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32"++
             ":32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32"

header = "target datalayout = " ++ show datalayout 
--------------------------------------------------------------------------------


genCode :: Program -> String
genCode p = let (_,e) = runEnv p
            in unlines (header : code e)

runEnv :: Program -> ((),Env)
runEnv (Program topDefs) = runState (mapM_ topdefCode topDefs) emptyEnv


--------------------------------------------------------------------------------
-- State modifiers
--------------------------------------------------------------------------------
addVar :: Type -> Ident -> Result ()
addVar t (Ident id) = putCode ["%"++ id ++ " = alloca " ++ llvmType t]

-- |Add code to the scope
putCode :: [String] -> Result ()
putCode ss = modify (\s -> s {code = (code s ++ ss)})
--------------------------------------------------------------------------------


topdefCode :: TopDef -> Result ()
topdefCode (FnDef t (Ident id) args (Block bs)) = 
 do
  putCode ["define " ++ llvmType t ++ " @" ++ id ++ "(" ++ {- ARGS -} ") {"]
  mapM_ stmtCode bs
  putCode ["}"]
                     

--------------------------------------------------------------------------------
-- Statement Code Generation.
--------------------------------------------------------------------------------
-- | Generate LLVM code for a Javalette Statement
stmtCode :: Stmt -> Result ()
stmtCode stmt = case stmt of
  Empty                             -> undefined
  (BStmt (Block ss))                -> undefined
  Decl t is                         -> case is of
                                         [] -> return ()
                                         (NoInit id:is') -> addVar t id >> alloca t
                                         _               -> undefined
  Ass id e@(TExp t e')              -> undefined
  Incr id                           -> undefined
  Decr id                           -> undefined
  Ret e@(TExp t _)                  -> exprCode e >> modify (\e -> e {code = init (code e) ++
                                                                             ["ret " ++ last (code e)]})
  VRet                              -> vret
  Cond (TExp Bool ELitTrue)    s    -> stmtCode s
  Cond (TExp Bool ELitFalse)   _    -> return ()
  Cond expr stmt                    -> undefined
  CondElse (TExp Bool ELitTrue) s _ -> stmtCode s
  CondElse (TExp Bool ELitFalse) _ s-> stmtCode s
  CondElse expr s0 s1               -> undefined
  While expr stmt                   -> undefined
  SExp e@(TExp t e')                -> undefined
  ArrAss id ds0 e@(TExp t _)        -> undefined
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Expression Code Generation.
--------------------------------------------------------------------------------
-- | Generate LLVM code for an expression
exprCode :: Expr -> Result ()
exprCode (TExp t e) = case e of
  EVar id      -> undefined
  ELitInt i    -> putCode ["i32 " ++ show i]
  ELitDoub d   -> putCode ["d32 " ++ show d]
  ELitTrue     -> putCode ["i32 1"]
  ELitFalse    -> putCode ["i32 0"]
  EApp id es   -> undefined
  EString s    -> undefined
  Neg exp      -> undefined
  Not exp      -> undefined
  EMul e0 o e1 -> undefined
  EAdd e0 o e1 -> undefined
  ERel e0@(TExp t' _) o e1 -> undefined
  EAnd e0 e1               -> undefined
  EOr  e0 e1               -> undefined
  EArr    t  [EDimen e]    -> undefined
  EArr    t'  ds           -> undefined
  EArrLen id               -> undefined
  EArrMDLen id ds          -> undefined
  EArrIdx id [EDimen e]    -> undefined
  EArrIdx id ds            -> undefined
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- LLVM Instructions.
--------------------------------------------------------------------------------

alloca t = putCode ["alloca " ++ llvmType t]
vret     = putCode ["ret void"]
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Utils.
--------------------------------------------------------------------------------
llvmType :: Type -> String
llvmType Int = "i32"
llvmType Doub = "d32"
llvmType Void = "void"
llvmType _ = undefined