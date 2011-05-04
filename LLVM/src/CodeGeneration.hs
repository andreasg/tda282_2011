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
header = "target datalayout = " ++ show datalayout ++ "\n"
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Run Functions
--------------------------------------------------------------------------------
genCode :: Program -> String
genCode p = let (_,e) = runEnv p
            in  unlines (header : (reverse $ code e))

runEnv :: Program -> ((),Env)
runEnv (Program topDefs) = runState (mapM_ topdefCode topDefs) emptyEnv
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- State modifiers
--------------------------------------------------------------------------------
addVar :: Type -> Ident -> Result ()
addVar t (Ident id) = instruction ["%"++ id ++ " = alloca " ++ llvmType t]

-- | Add code to the scope
putCode :: [String] -> Result ()
putCode s = modify (\e -> e {code = ((head $ code e)++(concat s)) : (drop 1 $ code e)})

newInstruction :: Result ()
newInstruction = modify (\s -> s {code = []:code s})

instruction :: [String] -> Result ()
instruction s = newInstruction >> putCode s
--------------------------------------------------------------------------------


topdefCode :: TopDef -> Result ()
topdefCode (FnDef t (Ident id) args (Block bs)) = 
 do
  instruction ["define " ++ llvmType t ++ " @" ++ id ++ "(" ++ {- ARGS -} ") {"]
  mapM_ stmtCode bs
  instruction ["}"]
                     

--------------------------------------------------------------------------------
-- Statement Code Generation.

type Register = String

load :: Ident -> Result Register
load = undefined

addi :: Register -> Integer -> Result Register
addi = undefined

storei :: Ident -> Register -> Result ()
storei = undefined
--------------------------------------------------------------------------------
-- | Generate LLVM code for a Javalette Statement
stmtCode :: Stmt -> Result ()
stmtCode stmt = case stmt of
  Empty                             -> return ()
  (BStmt (Block ss))                -> do modify (\s -> s {vars = ([]:vars s)})
                                          mapM_ stmtCode ss
                                          modify (\s -> s {vars = tail (vars s)})
  Decl t is                         -> case is of
                                         [] -> return ()
                                         (NoInit id:is') -> addVar t id
                                         _               -> undefined
  Ass id e@(TExp t e')              -> undefined
  Incr id                           -> do r1 <-load id
                                          r2 <- addi r1 1
                                          storei id r2
  Decr id                           -> undefined
  Ret e                             -> ret e
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
  ELitDoub d   -> putCode ["double " ++ show d]
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
alloca t = instruction ["alloca " ++ llvmType t]
vret     = instruction ["ret void"]
ret    e = newInstruction >> putCode ["ret "] >> exprCode e
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Utils.
--------------------------------------------------------------------------------
llvmType :: Type -> String
llvmType Int  = "i32"
llvmType Doub = "double"
llvmType Void = "void"
llvmType _    = undefined
--------------------------------------------------------------------------------