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
-- | An abstract representation of LLVM-values
data Value = VReg Type Register | VPtr Type Register | VInt Integer 
           | VDoub Double       | VBit Integer | VString Int String
instance Show Value where
    show (VReg t r) = llvmType t ++ " " ++  show r
    show (VPtr t r) = llvmType t ++ "* " ++ show r
    show (VInt i)   = llvmType Int ++ " " ++ show i
    show (VDoub d)  = llvmType Doub ++ " " ++ show d
    show (VBit i)   = "i1 " ++ show i
    show (VString len s) = "i8* getelementptr inbounds ([" ++ show (len+1) ++ " x i8]* @."++s++", i32 0, i32 0)"

data Register = Reg String
    deriving Eq
instance Show Register where
    show (Reg s) = "%"++s

-- | State type
type Result = State Env

-- | Environment used to keep track of all data during code-gen.
data Env = Env
  { nextRegister :: Int                -- next num for register/label gen
  , labelCount   :: Int                -- labels
  , strings      :: [String]   -- global string literals
  , vars         :: [[(Ident,Register)]] -- variables
  , funs         :: [(Ident,Type)]     -- function types
  , code         :: [String]
  }
emptyEnv :: Env
emptyEnv = Env 1 -- register count
               0  -- labels
               []  -- strings
               [ [],[] ] -- vars
               [] -- functions
               [] -- code

--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- File header and runtime-function declarations
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
            in  unlines (header : strings e  ++  (reverse $ code e))

runEnv :: Program -> ((),Env)
runEnv (Program topDefs) = runState (mapM_ topdefCode topDefs) emptyEnv
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- State modifiers
--------------------------------------------------------------------------------
addString s = do e <- get
                 let name = "str"++show (length $ strings e)
                 let s' = "@."++name ++ " = private constant [" ++ show (1 + length s) ++ " x i8] c\"" ++ s ++ "\\00\""
                 modify (\e -> e { strings = (s' : strings e) })
                 return name

-- | Add code to the scope
putCode :: [String] -> Result ()
putCode s = modify $ \e -> e {code = (concat s) : (code e)}

getLabel :: Result String
getLabel = do e <- get
              modify (\e -> e {labelCount = labelCount e + 1})
              return ("L" ++ show (labelCount e))

putLabel :: String -> Result ()
putLabel l  = putCode [l++":"]

newRegister :: Result Register
newRegister = do e <- get
                 modify $ \e -> e {nextRegister = nextRegister e + 1}
                 return (Reg (show $ nextRegister e))
--------------------------------------------------------------------------------

addVar :: Type -> Ident -> Result ()
addVar t id@(Ident n) = do r <- newRegister
                           modify $ \e -> e { vars = (((id, r) : head (vars e)) : tail (vars e))}
                           alloca r t
                           store (VReg t (Reg n)) (VPtr t r)

getVar :: Ident -> Type -> Result Value
getVar id@(Ident n) t = do s <- get
                           case dropWhile (==Nothing) (map (lookup id) (vars s)) of
                            (Just r:_) -> return (VPtr t r)
                            []             -> return (VPtr t (Reg n))


--------------------------------------------------------------------------------
-- Top level code generation
--------------------------------------------------------------------------------
topdefCode :: TopDef -> Result ()
topdefCode (FnDef t (Ident id) args (Block bs)) =
 do
  modify $ \e -> e {nextRegister = 1, vars = [[]]}
  putCode ["define " ++ llvmType t ++ " @" ++ id ++ "(" ++ f args ++ ") {"]

  -- create regestires and allocate space for all the arguments, and then load them.
  mapM_ (\(Arg t id) -> addVar t id) args

  mapM_ stmtCode bs
  putCode ["}"]

  where f xs = drop 2 $ foldl (\a (Arg t (Ident id)) -> a ++ ", " 
                               ++ (llvmType t ++ " %" ++ id)) [] xs
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Statement Code Generation.
--------------------------------------------------------------------------------
-- | Generate LLVM code for a Javalette Statement
stmtCode :: Stmt -> Result ()
stmtCode stmt = case stmt of
  Empty                             -> return ()
  (BStmt (Block ss))                -> do modify $ \e' -> e' { vars = ([] : vars e') }
                                          mapM_ stmtCode ss
                                          modify $ \e' -> e' {vars = tail (vars e')}
  Decl t is                         -> case is of
                                        [] -> return ()
                                        (NoInit (Ident id):is') -> 
                                           alloca (Reg id) t >> 
                                           stmtCode (Decl t is')
                                        (Init (Ident id) e:is') -> 
                                               do alloca (Reg id) t
                                                  v <- exprCode e
                                                  store v (VPtr t (Reg id))
                                                  stmtCode (Decl t is')
  Ass (Ident id) e@(TExp t e')      -> do r1 <- exprCode e
                                          store r1 (VPtr t (Reg id))
  Incr (Ident id)                   -> do r1 <- load (VPtr Int (Reg id))
                                          r2 <- add  (VInt 1)  r1
                                          store r2   (VPtr Int (Reg id))
  Decr (Ident id)                   -> do r1 <- load (VPtr Int (Reg id))
                                          r2 <- sub  (VInt 1) r1
                                          store r2   (VPtr Int (Reg id))
  Ret e                             -> ret e
  VRet                              -> vret
  Cond (TExp Bool ELitTrue)    s    -> stmtCode s
  Cond (TExp Bool ELitFalse)   _    -> return ()
  Cond expr stmt                    -> do true <- getLabel
                                          end <- getLabel
                                          v <- exprCode expr
                                          b <- cmp EQU v (VBit 1)
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
                                          comp <- cmp EQU v (VBit 1)
                                          br comp true false
                                          putLabel true
                                          stmtCode s0
                                          goto end
                                          putLabel false
                                          stmtCode s1
                                          goto end
                                          putLabel end
  SExp e@(TExp t e')                -> exprCode e >> return ()
  While expr stmt                   -> do begin <- getLabel
                                          loop  <- getLabel
                                          end   <- getLabel
                                          goto begin
                                          putLabel begin
                                          v <- exprCode expr
                                          comp <- cmp EQU v (VBit 1)
                                          br comp loop end
                                          putLabel loop
                                          stmtCode stmt
                                          goto begin
                                          putLabel end
  For t id0 id1 s                   -> undefined
  ArrAss id ds0 e@(TExp t _)        -> undefined
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Generate code for expressions
--------------------------------------------------------------------------------
exprCode :: Expr -> Result Value
exprCode (TExp t e) = case e of
  EVar id         -> do r <- getVar id t
                        load r
  ELitInt i       -> return $ VInt i
  ELitDoub d      -> return $ VDoub d
  ELitTrue        -> return $ VBit 1
  ELitFalse       -> return $ VBit 0
  EApp id es      -> do vs <- mapM exprCode es
                        call t id vs
  EAdd e0 o e1    -> do v1 <- exprCode e0
                        v2 <- exprCode e1
                        case o of Plus  -> add v1 v2
                                  Minus -> sub v1 v2
  EMul e0 op e1   -> do v1 <- exprCode e0
                        v2 <- exprCode e1
                        case op of
                          Div   -> div' v1 v2
                          Mod   -> rem' v1 v2
                          Times -> mul' v1 v2
  ERel e0 op e1   -> do v1 <- exprCode e0
                        v2 <- exprCode e1
                        cmp op v1 v2
  EString str     -> do name <- addString str
                        return (VString (length str) name)
  EAnd e0 e1      -> do true0 <- getLabel
                        true1 <- getLabel
                        false <- getLabel
                        end   <- getLabel
                     
                        r <- newRegister
                        alloca r Bool
                  
                        v0 <- exprCode e0
                        x_cmp <- cmp EQU v0 (VBit 0)
                        br x_cmp false true0
                     
                        putLabel false
                        store (VBit 0) (VPtr Bool r)
                        goto end
                     
                        putLabel true0
                        v1 <- exprCode e1
                        y_cmp <- cmp EQU v1 (VBit 0)
                        br y_cmp false true1
                        
                        putLabel true1
                        store (VBit 1) (VPtr Bool r)
                        goto end
                     
                        putLabel end
                        load (VPtr Bool r)
  EOr  e0 e1      -> do true  <- getLabel
                        false0 <- getLabel
                        false1 <- getLabel
                        end   <- getLabel
                        r <- newRegister
                        alloca r Bool
                                 
                        v0 <- exprCode e0
                        x_cmp <- cmp NE v0 (VBit 0)
                        br x_cmp true false0
                      
                        putLabel false0 -- x == false
                        v1 <- exprCode e1
                        y_cmp <- cmp NE v1 (VBit 0)
                        br y_cmp true false1
                      
                        putLabel true
                        store (VBit 1) (VPtr Bool r)
                        goto end
                      
                        putLabel false1
                        store (VBit 0) (VPtr Bool r)
                        goto end
                        
                        putLabel end
                        load (VPtr Bool r)
  Neg e           -> do v <- exprCode e
                        sub zero v
                        where zero = if t == Doub then VDoub 0.0 else VInt 0
  Not e           -> do v <- exprCode e
                        xor v (VBit 1)
{-
 | EArr Type [ArrDimen]
 | EArrIdx Ident [ArrDimen]
 | EArrLen Ident
 | EArrMDLen Ident [ArrDimen]
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
br cond iftrue iffalse = putCode [ "br i1 " ++ unValue cond
                                 , ", label %" ++ iftrue
                                 , ", label %" ++ iffalse]

binOp :: Value -> Value -> String -> Type -> Result Value
binOp op1 op2 fun t = do r <- newRegister
                         putCode [ show r ++ " = " ++ fun ++ " " ++ llvmType t ++ " "
                                 , unValue op1 ++ ", " ++ unValue op2]
                         return (VReg t r)

add :: Value -> Value -> Result Value
add op1 op2 = binOp op1 op2 op t
     where (op,t) = if isInts op1 op2 then ("add",Int) else ("fadd", Doub)

sub :: Value -> Value -> Result Value
sub op1 op2 = binOp op1 op2 op t
     where (op,t) = if isInts op1 op2 then ("sub",Int) else ("fsub", Doub)

mul' :: Value -> Value -> Result Value
mul' op1 op2 = binOp op1 op2 op t
     where (op,t) = if isInts op1 op2 then ("mul",Int) else ("fmul", Doub)

div' :: Value -> Value -> Result Value
div' op1 op2 =  binOp op1 op2 op t
     where (op,t) = if isInts op1 op2 then ("sdiv",Int) else ("fdiv", Doub)

rem' :: Value -> Value -> Result Value
rem' op1 op2 = binOp op1 op2 op t
     where (op,t) = if isInts op1 op2 then ("srem",Int) else ("frem", Doub)

cmp :: RelOp -> Value -> Value -> Result Value
cmp op v1 v2 = do r <- newRegister
                  putCode [ show r ++ " = " ++ f ++ " " ++ op' ++ " "
                          , show v1 ++ ", " ++ unValue v2]
                  return (VReg Bool r)
    where (t,f) = if isInts v1 v2 then (Int,"icmp") else (Doub,"fcmp")
          op' = case t of
                  Int  -> case op of EQU -> "eq";  NE  -> "ne";  LTH -> "slt"
                                     GTH -> "sgt"; LE  -> "sle"; GE  -> "sge"
                  Doub -> case op of EQU -> "oeq";  NE  -> "one";  LTH -> "olt"
                                     GTH -> "ogt"; LE  -> "ole"; GE  -> "oge"

call :: Type -> Ident -> [Value] -> Result Value
call Void (Ident id) vs = do putCode ["call void @" ++ id ++"("++f vs++")"]
                             return (VInt 0)
    where f xs = drop 2 $ foldl (\a x -> a ++ ", " ++ show x) [] xs                                     
call t (Ident id) vs = do r <- newRegister
                          putCode [ show r ++ " = call " ++ llvmType t
                                  , " @" ++ id ++ "(" ++f vs ++ ")"]
                          return (VReg t r)
    where f xs = drop 2 $ foldl (\a x -> a ++ ", " ++ show x) [] xs

alloca :: Register -> Type -> Result ()
alloca dest t = putCode [show dest ++ " = alloca " ++ llvmType t]

load :: Value -> Result Value
load ptr@(VPtr t _) = do r <- newRegister
                         putCode [show r ++ " = load " ++ show ptr]
                         return (VReg t r)

store :: Value -> Value -> Result ()
store op ptr  = putCode ["store "  ++ show op ++ ", " ++ show ptr]

xor :: Value -> Value -> Result Value
xor v0 v1 = binOp v0 v1 "xor" Bool

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
unValue (VInt i)   = show i
unValue (VDoub d)  = show d
unValue (VBit i )  = show i

-- | Determine if a LLVM value is of Integer type
isInt :: Value -> Bool
isInt (VReg Int _)  = True
isInt (VReg Bool _) = True
isInt (VReg _ _)    = False
isInt (VPtr _ _)    = False
isInt (VInt _)      = True
isInt (VDoub _)     = False
isInt (VBit i)      = True

isInts :: Value -> Value -> Bool
isInts a b = isInt a && isInt b
--------------------------------------------------------------------------------