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
data Value = VReg LLVMType Register | VInt Integer
           | VDoub Double           | VBit Integer           | VString Int String
           | VVec Register          | VType String

data LLVMType = Prim Type | Ptr LLVMType | Vector | I8
              deriving (Eq)

instance Show LLVMType where
    show t = case t of
               Prim t -> llvmType t
               Ptr ts -> show ts ++ "*"
               I8     -> "i8"
               Vector -> "%struct.vector*"

instance Show Value where
    show (VReg t r) = show t ++ " " ++  show r
--    show (VPtr t r) = show t ++ "* " ++ show r
    show (VInt i)   = show (Prim Int) ++ " " ++ show i
    show (VDoub d)  = show (Prim Doub) ++ " " ++ show d
    show (VBit i)   = "i1 " ++ show i
    show (VType s)  = s
    show (VString len s) = "i8* getelementptr inbounds ([" ++ show (len+1) ++ " x i8]* @."++s++", i32 0, i32 0)"

valueType (VReg t _) = show t
--valueType (VPtr t _) = show t ++ "*"
valueType (VInt _)   = show (Prim Int)
valueType (VDoub _)  = show (Prim Doub)
valueType (VBit _)   = "i1"
valueType (VString _ _) = "i8*"
valueType (VVec _)     = "i8**"

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
  , vars         :: [[(Ident,(LLVMType,Register))]] -- variables
  , funs         :: [(Ident,LLVMType)]     -- function types
  , code         :: [String]
  }
emptyEnv :: Env
emptyEnv = Env 1    -- register count
               0    -- labels
               []   -- strings
               [[]] -- vars
               []   -- functions
               []   -- code

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
         "declare i8* @calloc(i32, i32)\n" ++
         "declare double @readDouble()\n\n" ++
         "%struct.vector = type {i32, i8**}\n\n"
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Run Functions
--------------------------------------------------------------------------------
-- | Generate LLVM code for Javalette
genCode :: Program -> String
genCode p = let (_,e) = runEnv p
            in  unlines (header : strings e  ++  (reverse $ code e))

-- | Render an environment.
runEnv :: Program -> ((),Env)
runEnv (Program topDefs) = runState (mapM_ topdefCode topDefs) emptyEnv
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- State modifiers
--------------------------------------------------------------------------------
-- | Add a string to the global scope.
addString s = do e <- get
                 let name = "str"++show (length $ strings e)
                 let s' = "@."++name ++ " = private constant [" ++ show (1 + length s) ++ " x i8] c\"" ++ s ++ "\\00\""
                 modify (\e -> e { strings = (s' : strings e) })
                 return name

-- | Add code to the Environment.
putCode :: [String] -> Result ()
putCode s = modify $ \e -> e {code = (concat s) : (code e)}

-- | Get a new, unused label.
getLabel :: Result String
getLabel = do e <- get
              modify (\e -> e {labelCount = labelCount e + 1})
              return ("L" ++ show (labelCount e))

-- | Put a label in the code.
putLabel :: String -> Result ()
putLabel l  = putCode [l++":"]

-- | Get a new, unused register.
newRegister :: Result Register
newRegister = do e <- get
                 modify $ \e -> e {nextRegister = nextRegister e + 1}
                 return (Reg ('v' : (show $ nextRegister e)))

-- | Register a new variable with the Environment.
addVar :: LLVMType -> Ident -> Result Value
addVar t id@(Ident n) = do r <- newRegister
                           modify $ \e -> e { vars = (((id, (t,r)) : head (vars e)) : tail (vars e))}
                           return (VReg (Ptr t) r)

-- | Retrieve a pointer to a variable.
getVar :: Ident -> Result Value
getVar id@(Ident n) = do s <- get
                         case dropWhile (==Nothing) (map (lookup id) (vars s)) of
                            (Just (t,r):_) -> return (VReg (Ptr t) r)
                            []             -> undefined --return (VPtr t (Reg n))
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Top level code generation
--------------------------------------------------------------------------------
topdefCode :: TopDef -> Result ()
topdefCode (FnDef t (Ident id) args (Block bs)) =
 do
  modify $ \e -> e {nextRegister = 1, vars = [[]]}
  putCode ["define " ++ show (Prim t) ++ " @" ++ id ++ "(" ++ f args ++ ") {"]
  mapM_ (\(Arg t (Ident id)) -> do var@(VReg t' r) <- addVar (Prim t) (Ident id)
                                   alloca r (Prim t)
                                   store (VReg (Prim t) (Reg id)) var) args
  mapM_ stmtCode bs
  putCode ["}"]

  where f xs = drop 2 $ foldl (\a (Arg t (Ident id)) -> a ++ ", "
                               ++ (show (Prim t) ++ " %" ++ id)) [] xs
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
                                        (NoInit id:is') -> do (VReg t' r) <- addVar (Prim t) id
                                                              alloca r (Prim t)
                                                              stmtCode (Decl t is')
                                        (Init id e:is') ->
                                               do v <- exprCode e
                                                  var@(VReg t' r) <- addVar (Prim t) id
                                                  alloca r (Prim t)
                                                  store v var
                                                  stmtCode (Decl t is')
  Ass id e@(TExp t e')      -> do r1 <- exprCode e
                                  var <- getVar id
                                  store r1 var
  Incr  id                          -> do var <- getVar id
                                          r1 <- load var
                                          r2 <- add  (VInt 1)  r1
                                          store r2   var --(VPtr Int (Reg id))
  Decr id                           -> do var <- getVar id
                                          r1 <- load var
                                          r2 <- sub r1 (VInt 1)
                                          store r2 var
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
  CondElse expr s0 s1               -> do if returns [s0] && returns [s1]
                                           then do true <- getLabel
                                                   false <- getLabel
                                                   v    <- exprCode expr
                                                   comp <- cmp EQU v (VBit 1)
                                                   br comp true false
                                                   putLabel true
                                                   stmtCode s0
                                                   putLabel false
                                                   stmtCode s1
                                           else do true <- getLabel
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
-- | Generate LLVM code for a Javalette expressoin. It will return a Value
-- | containing the result of the expression.
exprCode :: Expr -> Result Value
exprCode (TExp t e) = case e of
  EVar id         -> do r <- getVar id
                        load r
  ELitInt i       -> return $ VInt i
  ELitDoub d      -> return $ VDoub d
  ELitTrue        -> return $ VBit 1
  ELitFalse       -> return $ VBit 0
  EApp id es      -> do vs <- mapM exprCode es
                        call (Prim t) id vs
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
                        alloca r (Prim Bool)

                        v0 <- exprCode e0
                        x_cmp <- cmp EQU v0 (VBit 0)
                        br x_cmp false true0

                        putLabel false
                        store (VBit 0) (VReg (Ptr (Prim Bool)) r)
                        goto end

                        putLabel true0
                        v1 <- exprCode e1
                        y_cmp <- cmp EQU v1 (VBit 0)
                        br y_cmp false true1

                        putLabel true1
                        store (VBit 1) (VReg (Ptr (Prim Bool)) r)
                        goto end

                        putLabel end
                        load (VReg (Ptr (Prim Bool)) r)
  EOr  e0 e1      -> do true  <- getLabel
                        false0 <- getLabel
                        false1 <- getLabel
                        end   <- getLabel
                        r <- newRegister
                        alloca r (Prim Bool)

                        v0 <- exprCode e0
                        x_cmp <- cmp NE v0 (VBit 0)
                        br x_cmp true false0

                        putLabel false0 -- x == false
                        v1 <- exprCode e1
                        y_cmp <- cmp NE v1 (VBit 0)
                        br y_cmp true false1

                        putLabel true
                        store (VBit 1) (VReg (Ptr (Prim Bool)) r)
                        goto end

                        putLabel false1
                        store (VBit 0) (VReg (Ptr (Prim Bool)) r)
                        goto end

                        putLabel end
                        load (VReg (Ptr (Prim Bool)) r)
  Neg e           -> do v <- exprCode e
                        sub zero v
                        where zero = if t == Doub then VDoub 0.0 else VInt 0
  Not e           -> do v <- exprCode e
                        xor v (VBit 1)
  EArr t [EDimen e] -> do len <- exprCode e
                          newvec len (Prim t)
  EArrLen id        -> getVar id >>= veclen
                       
                       
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

binOp :: Value -> Value -> String -> LLVMType -> Result Value
binOp op1 op2 fun t = do r <- newRegister
                         putCode [ show r ++ " = " ++ fun ++ " " ++ show t ++ " "
                                 , unValue op1 ++ ", " ++ unValue op2]
                         return (VReg t r)

add :: Value -> Value -> Result Value
add op1 op2 = binOp op1 op2 op t
     where (op,t) = if isInts op1 op2 then ("add",(Prim Int)) else ("fadd", (Prim Doub))

sub :: Value -> Value -> Result Value
sub op1 op2 = binOp op1 op2 op t
     where (op,t) = if isInts op1 op2 then ("sub",(Prim Int)) else ("fsub", (Prim Doub))

mul' :: Value -> Value -> Result Value
mul' op1 op2 = binOp op1 op2 op t
     where (op,t) = if isInts op1 op2 then ("mul",(Prim Int)) else ("fmul", (Prim Doub))

div' :: Value -> Value -> Result Value
div' op1 op2 =  binOp op1 op2 op t
     where (op,t) = if isInts op1 op2 then ("sdiv",(Prim Int)) else ("fdiv", (Prim Doub))

rem' :: Value -> Value -> Result Value
rem' op1 op2 = binOp op1 op2 op t
     where (op,t) = if isInts op1 op2 then ("srem",(Prim Int)) else ("frem", (Prim Doub))

cmp :: RelOp -> Value -> Value -> Result Value
cmp op v1 v2 = do r <- newRegister
                  putCode [ show r ++ " = " ++ f ++ " " ++ op' ++ " "
                          , show v1 ++ ", " ++ unValue v2]
                  return (VReg (Prim Bool) r)
    where (t,f) = if isInts v1 v2 then (Int,"icmp") else (Doub,"fcmp")
          op' = case t of
                  Int  -> case op of EQU -> "eq";  NE  -> "ne";  LTH -> "slt"
                                     GTH -> "sgt"; LE  -> "sle"; GE  -> "sge"
                  Doub -> case op of EQU -> "oeq";  NE  -> "one";  LTH -> "olt"
                                     GTH -> "ogt"; LE  -> "ole"; GE  -> "oge"

call :: LLVMType -> Ident -> [Value] -> Result Value
call (Prim Void) (Ident id) vs = do putCode ["call void @" ++ id ++"("++f vs++")"]
                                    return (VInt 0)
    where f xs = drop 2 $ foldl (\a x -> a ++ ", " ++ show x) [] xs
call t (Ident id) vs = do r <- newRegister
                          putCode [ show r ++ " = call " ++ show t
                                  , " @" ++ id ++ "(" ++f vs ++ ")"]
                          return (VReg t r)
    where f xs = drop 2 $ foldl (\a x -> a ++ ", " ++ show x) [] xs

alloca :: Register -> LLVMType -> Result ()
alloca dest t = putCode [show dest ++ " = alloca " ++ show t]

load :: Value -> Result Value
load ptr@(VReg (Ptr t) _) = do r <- newRegister
                               putCode [show r ++ " = load " ++ show ptr]
                               return (VReg t r)

store :: Value -> Value -> Result ()
store op ptr  = putCode ["store "  ++ show op ++ ", " ++ show ptr]

xor :: Value -> Value -> Result Value
xor v0 v1 = binOp v0 v1 "xor" (Prim Bool)


calloc :: Value -> Value  -> Result Value
calloc n size = do r0 <- newRegister
                   putCode [show r0 ++ " = call i8* @calloc("++ show n ++ ", " ++ show size ++ ")"]
                   return (VReg (Ptr I8) r0)

bitcast :: Value -> LLVMType -> Result Value
bitcast v t = do r <- newRegister
                 putCode [show r ++ " = bitcast " ++ show v ++ " to " ++ show t]
                 return (VReg t r)

setelem :: Value -> Value -> Value -> Type ->  Result ()
setelem vector index elem t = do e <- newRegister
                                 r0 <- newRegister
                                 putCode [show e ++ " = bitcast " ++ show t ++ " to i8*"]
                                 putCode [show r0 ++ " = getelementptr inbounds " ++ show vector ++ ", i32 0, i32 1"]
                                 r1 <- load (VVec r0)
                                 r2 <- newRegister
                                 putCode [show r2 ++ " = getelementptr inbounds " ++ show  index]
                                 store elem (VVec r2)
                                 return ()

getelem :: Value -> Value -> LLVMType -> Result Value
getelem vector index t = do r0 <- newRegister
                            putCode [show r0 ++ " = getelementptr inbounds " ++ show vector ++ ", i32 0, i32 1"]
                            r1 <- load (VVec r0)
                            r2 <- newRegister
                            putCode [show r2 ++ " = getelementptr inbounds " ++ show r1 ++ ", " ++ show index]
                            r3 <- load (VVec r2)
                            elem <- newRegister
                            putCode [show elem ++ " = bitcast " ++ show r3 ++ " to " ++ show t]
                            return (VReg t elem)
sizeof :: LLVMType -> Result Value
sizeof t = do r0 <- newRegister
              putCode [show r0 ++ " = getelementptr " ++ show (Ptr t) ++ " null, i32 1"]
              r1 <- newRegister
              putCode [show r1 ++ " = ptrtoint " ++ show (Ptr t) ++ " " ++ show r0 ++ " to i32"]
              return (VReg (Prim Int) r1)

newvec :: Value -> LLVMType -> Result Value
newvec len t= do vec <- newRegister
                 alloca vec Vector
                 sz <- sizeof t
                 r0 <- calloc len sz
                 r1 <- bitcast r0 Vector
                 store r1 (VReg (Ptr Vector) vec)
                 v0 <- load (VReg (Ptr Vector) vec)
                 r2 <- newRegister
                 putCode [show r2 ++ " = getelementptr inbounds " ++ show v0 ++ ", i32 0, i32 0"]
                 store len (VReg (Ptr (Prim Int)) r2)
                 r3 <- load (VReg (Ptr Vector) vec)
                 return r3

veclen :: Value -> Result Value
veclen vec = do l <- newRegister
                vec0 <- load vec
                putCode [show l ++ " = getelementptr inbounds " ++ show vec0 ++ ", i32 0, i32 0"]
                len <- load (VReg (Ptr (Prim Int)) l)
                return len
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Utils.
--------------------------------------------------------------------------------
-- | Get the LLVM repr. of a Javalette type.
llvmType :: Type -> String
llvmType Int = "i32"
llvmType Doub = "double"
llvmType Void = "void"
llvmType Bool = "i1"
llvmType (ArrInt _) = "%struct.vector*"
llvmType (ArrDoub _) = "%struct.vector*"
llvmType _    = undefined

-- | Get the string repr. of a Value without it's type.
unValue :: Value -> String
unValue (VReg _ r) = show r
unValue (VInt i)   = show i
unValue (VDoub d)  = show d
unValue (VBit i )  = show i

-- | Determine if a LLVM value is of Integer type
isInt :: Value -> Bool
isInt (VReg (Prim Int) _)  = True
isInt (VReg (Prim Bool) _) = True
isInt (VReg (Ptr (Prim Int))  _)  = True
isInt (VReg (Ptr (Prim Bool)) _) = True
isInt (VReg t _) = False
isInt (VInt _)      = True
isInt (VDoub _)     = False
isInt (VBit i)      = True

isInts :: Value -> Value -> Bool
isInts a b = isInt a && isInt b
--------------------------------------------------------------------------------