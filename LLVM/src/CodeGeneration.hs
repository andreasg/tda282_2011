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
data Value = VReg Type Register | VPtr Type Register | VInt Integer | VDoub Double | VBit Integer
instance Show Value where
    show (VReg t r) = llvmType t ++ " " ++  show r
    show (VPtr t r) = llvmType t ++ "* " ++ show r
    show (VInt i) = llvmType Int ++ " " ++ show i
    show (VDoub d) = llvmType Doub ++ " " ++ show d
    show (VBit i) = "i1 " ++ show i
data Register = Reg String
instance Show Register where
    show (Reg s) = "%"++s


type Result = State Env

-- | Environment used to keep track of all data during code-gen.
data Env = Env
  { nextRegister :: Int                -- next num for register/label gen
  , labelCount   :: Int                -- labels
  , strings      :: [(Ident,String)]   -- global string literals
  , vars         :: [[(Ident,String)]] -- variables
  , funs         :: [(Ident,Type)]     -- function types
  , code         :: [String]
  }
emptyEnv :: Env
emptyEnv = Env 1 0 [] [] [] []
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- File header
--------------------------------------------------------------------------------
datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32"++
             ":32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32"
header = "target datalayout = " ++ show datalayout ++ "\n" ++
         "declare void @printInt(i32)\n" ++
         "declare void @printDouble(double)\n" ++
         "declare void @printString(i8*)\n" ++
         "declare i32 @readInt()\n" ++
         "declare double @readDouble()\n\n"
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

getLabel :: Result String
getLabel = do e <- get
              modify (\e -> e {labelCount = labelCount e + 1})
              return ("L" ++ show (labelCount e))

putLabel l  = putCode [l++":"]

newRegister :: Result Register
newRegister = do e <- get
                 modify $ \e -> e {nextRegister = nextRegister e + 1}
                 return (Reg (show $ nextRegister e))
--------------------------------------------------------------------------------


topdefCode :: TopDef -> Result ()
topdefCode (FnDef t (Ident id) args (Block bs)) =
 do
  putCode ["define " ++ llvmType t ++ " @" ++ id ++ "(" ++ f args ++ ") {"]
  mapM_ stmtCode bs
  putCode ["}"]

  where f xs = drop 2 $ foldl (\a (Arg t (Ident id)) -> a ++ ", " ++ (llvmType t ++ " %" ++ id)) [] xs


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
                                         (NoInit (Ident id):is') -> alloca (Reg id) t >> stmtCode (Decl t is')
                                         (Init (Ident id) e:is') -> do alloca (Reg id) t
                                                                       v <- exprCode e
                                                                       store v (VPtr t (Reg id))
                                                                       stmtCode (Decl t is')
  Ass (Ident id) e@(TExp t e')      -> do r1 <- exprCode e
                                          store r1 (VPtr t (Reg id))
  Incr (Ident id)                   -> do r1 <- load (VPtr Int (Reg id))
                                          r2 <- add (VInt 1)  r1
                                          store r2 (VPtr Int (Reg id))
  Decr (Ident id)                   -> do r1 <- load (VPtr Int (Reg id))
                                          r2 <- sub (VInt 1) r1
                                          store r2 (VPtr Int (Reg id))
  Ret e                             -> ret e
  VRet                              -> vret
  Cond (TExp Bool ELitTrue)    s    -> stmtCode s
  Cond (TExp Bool ELitFalse)   _    -> return ()
  Cond expr stmt                    -> do true <- getLabel
                                          end <- getLabel
                                          v <- exprCode expr
                                          b <- icmp "eq" v (VBit 1)
                                          br b true end
                                          putLabel true
                                          stmtCode stmt
                                          goto end
                                          putLabel end
  CondElse (TExp Bool ELitTrue) s _ -> stmtCode s
  CondElse (TExp Bool ELitFalse) _ s-> stmtCode s
  CondElse expr s0 s1               -> do true <- getLabel
                                          false <- getLabel
                                          end <- getLabel
                                          v <- exprCode expr
                                          comp <- icmp "eq" v (VBit 1)
                                          br comp true false
                                          putLabel true
                                          stmtCode s0
                                          goto end
                                          putLabel false
                                          stmtCode s1
                                          goto end
                                          putLabel end
  SExp e@(TExp t e')                -> exprCode e >> return ()
  While expr stmt                   -> undefined
  For t id0 id1 s                   -> undefined
  ArrAss id ds0 e@(TExp t _)        -> undefined
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Generate code for expressions
--------------------------------------------------------------------------------
exprCode :: Expr -> Result Value
exprCode (TExp t e) = case e of
  EVar (Ident id) -> load (VPtr t (Reg id))
  ELitInt i       -> return $ VInt i
  ELitDoub d      -> return $ VDoub d
  ELitTrue        -> return $ VInt 1
  ELitFalse       -> return $ VInt 0
  EApp id es      -> do vs <- mapM exprCode es
                        call t id vs
  EAdd e0 o e1    -> do v1 <- exprCode e0
                        v2 <- exprCode e1
                        case o of Plus  -> add v1 v2
                                  Minus -> sub v1 v2
  EMul e0 op e1   -> undefined {-case op of
                       Div   -> 
                       Mod   -> 
                       Times -> -}
  ERel e0 o e1   -> do v1 <- exprCode e0
                       v2 <- exprCode e1
                       icmp op v1 v2
    where op = case o of
                 EQU -> "eq"
                 NE  -> "ne"
                 LTH -> "slt"
                 GTH -> "sgt"
                 LE  -> "ule"
                 GE  -> "sge"
  EAnd e0 e1      -> undefined
  EOr  e0 e1      -> undefined

{-
 | EArr Type [ArrDimen]
 | EArrIdx Ident [ArrDimen]
 | EArrLen Ident
 | EArrMDLen Ident [ArrDimen]
 | EString String
 | Neg Expr
 | Not Expr
-}
  _  -> undefined
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- LLVM Instructions.
--------------------------------------------------------------------------------
vret :: Result ()
vret  = putCode ["ret void"]

ret :: Expr -> Result ()
ret e@(TExp t _) = do v <- exprCode e
                      putCode ["ret " ++ show v]
                      return ()

goto :: String -> Result ()
goto l = putCode ["br label %" ++ l]

br :: Value -> String -> String -> Result ()
br cond iftrue iffalse = putCode [ "br i1 "
                                 , unValue cond
                                 , ", label %" ++ iftrue
                                 , ", label %" ++ iffalse]

add :: Value -> Value -> Result Value
add op1 op2 = do r <- newRegister
                 putCode [ show r ++ " = " ++ op ++ " "
                         , show op1 ++ ", " ++ unValue op2]
                 return (VReg t r)
          where t = if isInt op1 then Int else Doub
                op = if isInt op1 then "add" else "fadd"

sub :: Value -> Value -> Result Value
sub op1 op2 = do r <- newRegister
                 putCode [ show r ++ " = " ++ op ++ " "
                         , show op1 ++ ", " ++ unValue op2]
                 return (VReg t r)
          where t = if isInt op1 then Int else Doub
                op = if isInt op1 then "sub" else "fsub"

icmp :: String -> Value -> Value -> Result Value
icmp cond op1 op2 = do r <- newRegister
                       putCode [ show r ++ " = icmp " ++ cond ++ " "
                               , " " ++ show op1 ++ ", " ++ unValue op2]
                       return (VReg Bool r)

call :: Type -> Ident -> [Value] -> Result Value
call t (Ident id) vs = do r <- newRegister
                          putCode [ head r ++ "call " ++ llvmType t ++ " @" ++ id ++ "("
                                  , f vs
                                  , ")"]
                          return (VReg t r)
    where head r = if t == Void then "" else show r ++ " = "
          f xs = drop 2 $ foldl (\a x -> a ++ ", " ++ show x) [] xs

alloca :: Register -> Type -> Result ()
alloca dest t = putCode [show dest ++ " = alloca " ++ llvmType t]

load :: Value -> Result Value
load ptr@(VPtr t _) = do r <- newRegister
                         putCode [show r ++ " = load " ++ show ptr]
                         return (VReg t r)

store :: Value -> Value -> Result ()
store op ptr  = putCode ["store "  ++ show op ++ ", " ++ show ptr]
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Utils.
--------------------------------------------------------------------------------
-- | Get the LLVM repr. of a Javalette type.
llvmType :: Type -> String
llvmType Int  = "i32"
llvmType Doub = "double"
llvmType Void = "void"
llvmType Bool = "i1"
llvmType _    = undefined


-- | Get the string repr. of a Value without it's type.
unValue :: Value -> String
unValue (VPtr _ r) = show r
unValue (VReg _ r) = show r
unValue (VInt i) = show i
unValue (VDoub d) = show d
unValue (VBit i ) = show i


isInt :: Value -> Bool
isInt (VReg Int _) = True
isInt (VPtr _ _)   = False
isInt (VInt _)     = True
isInt (VDoub _)    = False
isInt (VBit i)     = True
--------------------------------------------------------------------------------