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
data Value = VReg Type Register | VPtr Type Register | VInt Integer | VDoub Double
instance Show Value where 
    show (VReg t r) = llvmType t ++ " " ++  show r
    show (VPtr t r) = llvmType t ++ "* " ++ show r
    show (VInt i) = llvmType Int ++ " " ++ show i
    show (VDoub d) = llvmType Doub ++ " " ++ show d
data Register = Reg String
instance Show Register where
    show (Reg s) = "%"++s


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
emptyEnv = Env 1 [] [] [] []
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
-- | Add code to the scope
putCode :: [String] -> Result ()
putCode s = modify $ \e -> e {code = (concat s) : (code e)}

newRegister :: Result Register
newRegister = do e <- get
                 modify $ \e -> e {nextRegister = nextRegister e + 1}
                 return (Reg (show $ nextRegister e))
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
  Empty                             -> return ()
  (BStmt (Block ss))                -> do modify (\s -> s {vars = ([]:vars s)})
                                          mapM_ stmtCode ss
                                          modify (\s -> s {vars = tail (vars s)})
  Decl t is                         -> case is of
                                         [] -> return ()
                                         (NoInit (Ident id):is') -> alloca (Reg id) t
                                         _                       -> undefined
  Ass (Ident id) e@(TExp t e')      -> do r1 <- valueExpr e
                                          store r1 (VPtr t (Reg id))

{-
                                     case e' of
                                         ELitInt i  -> store  (VInt i) (VPtr Int (Reg id))
                                         ELitDoub d -> store  (VDoub d) (VPtr Doub (Reg id))
                                         ELitTrue   -> store  (VInt 1) (VPtr Int (Reg id))
                                         ELitFalse  -> store  (VInt 0) (VPtr Int (Reg id))
                                         _          -> undefined
-}
  Incr (Ident id)                   -> do r1 <- newRegister
                                          r1 <- load (VPtr Int (Reg id))
                                          r2 <- add (VInt 1)  r1
                                          store r2 (VPtr Int (Reg id))
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

int i = show $ VInt i
double d = show $ VDoub d
reg t r = show $ VReg t r 
ptr t r = show $ VPtr t r

unValue (VPtr _ r) = show r
unValue (VReg _ r) = show r
unValue (VInt i) = show i
unValue (VDoub d) = show d




--------------------------------------------------------------------------------
-- Expression Code Generation.
--------------------------------------------------------------------------------
-- | Generate LLVM code for an expression
exprCode :: Expr -> Result ()
exprCode (TExp t e) = case e of
  EVar (Ident id) -> putCode [reg t (Reg id)]
  ELitInt i    -> putCode [int i]
  ELitDoub d   -> putCode [double d]
  ELitTrue     -> putCode [int 1]
  ELitFalse    -> putCode [int 0]
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
-- Store the result of an expression in a register.
--------------------------------------------------------------------------------
valueExpr :: Expr -> Result Value
valueExpr (TExp t e) = case e of
  EVar (Ident id) -> load (VPtr t (Reg id))
  ELitInt i       -> return $ VInt i
  ELitDoub d      -> return $ VDoub d
  ELitTrue        -> return $ VInt 1
  ELitFalse       -> return $ VInt 0
  EApp id es      -> do vs <- mapM valueExpr es
                        call t id vs
                        return (VInt 1)


                     
  EAdd e0 o e1    -> do v1 <- valueExpr e0
                        v2 <- valueExpr e1
                        case o of Plus  -> add v1 v2
                                  Minus -> sub v1 v2
  _  -> undefined                     
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- LLVM Instructions.
--------------------------------------------------------------------------------
joinLines = modify $ \e -> e { code = ((concat $ (reverse $take 2 (code e))) : (drop 2 (code e)))}
-- terminator instruction
vret  = putCode ["ret void"]
ret e@(TExp t _) =  putCode ["ret "] >> exprCode e >> joinLines

-- | branch. Cond is a register, iftrue and iffalse are labels.
br cond iftrue iffalse = putCode [ "br i1 "
                                 , "%" ++ cond
                                 , ", label %" ++ iftrue
                                 , ", label %" ++ iffalse]
unreachable = putCode ["unreachable"]


-- binary operators
add op1 op2 = do r <- newRegister
                 putCode [ show r ++ " = add "
                         , show op1 ++ ", " ++ unValue op2]
                 return (VReg Int r)
sub op1 op2 = do r <- newRegister
                 putCode [ show r ++ " = sub "
                         , show op1 ++ ", " ++ unValue op2]
                 return (VReg Int r)

-- other operations
icmp cond t op1 op2 = do r <- newRegister 
                         putCode [ show r ++ " = icmp " ++ cond ++ " " ++ llvmType t
                                 , " " ++ show op1 ++ ", " ++ show op2]
                         return r

call t (Ident id) vs = do r <- newRegister
                          putCode [ show r ++ " = call @" ++ id ++ "("
                                  , f vs
                                  , ")"]
                          return r

    where f []     = []
          f (x:xs) = show x ++ ", " ++ f xs

-- memory access instructions
alloca dest t = putCode [show dest ++ " = alloca " ++ llvmType t]
load ptr@(VPtr t _) = do r <- newRegister 
                         putCode [show r ++ " = load " ++ show ptr]
                         return (VReg t r)
store op ptr  = putCode ["store "  ++ show op ++ ", " ++ show ptr]
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