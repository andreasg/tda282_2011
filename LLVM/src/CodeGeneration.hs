module CodeGeneration (genCode) where


--------------------------------------------------------------------------------
-- Imports.
--------------------------------------------------------------------------------
import AbsJavalette
import Control.Monad.State
import ReturnChecker
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Types and Data.
--------------------------------------------------------------------------------
-- | An abstract representation of LLVM-values
data Value = VReg LLVMType Register | VInt Integer
           | VDoub Double           | VBit Integer | VString Int String
instance Show Value where
    show (VReg t r) = show t ++ " " ++  show r
    show (VInt i)   = show (Prim Int) ++ " " ++ show i
    show (VDoub d)  = show (Prim Doub) ++ " " ++ show d
    show (VBit i)   = "i1 " ++ show i
    show (VString len s) = "i8* getelementptr inbounds ([" ++ show (len+1) ++
                           " x i8]* @."++s++", i32 0, i32 0)"

-- | Abstraction to allow for an extended set of Types
data LLVMType = Prim Type | Ptr LLVMType | Vector LLVMType | I8
              deriving (Eq)
instance Show LLVMType where
    show t = case t of
               Prim t -> showType t
               Ptr ts -> show ts ++ "*"
               I8     -> "i8"
               Vector t            -> "{i32, " ++ show t ++ "*}"

-- | Datatype for LLVM Registers
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
emptyEnv = Env 1 0 [] [[]] [] []
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
         "declare double @readDouble()\n\n"
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
                 let s' = "@."++name ++ " = private constant [" ++
                          show (1 + length s) ++ " x i8] c\"" ++ s ++ "\\00\""
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
addVar t id@(Ident n) =
   do r <- newRegister
      modify $ \e -> e { vars = (((id, (t,r)) : head (vars e)) : tail (vars e))}
      return (VReg (Ptr t) r)

-- | Retrieve a pointer to a variable.
getVar :: Ident -> Result Value
getVar id@(Ident n) = do 
  s <- get
  case dropWhile (==Nothing) (map (lookup id) (vars s)) of
    (Just (t,r):_) -> return (VReg (Ptr t) r)
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Top level code generation
--------------------------------------------------------------------------------
topdefCode :: TopDef -> Result ()
topdefCode (FnDef t (Ident id) args (Block bs)) =
 do
  modify $ \e -> e {nextRegister = 1, vars = [[]]}
  putCode ["define " ++ show (Prim t) ++ " @" ++ id ++ "(" ++ f args ++ ") {"]
  mapM_ (\(Arg t (Ident id)) -> do var@(VReg t' r) <- 
                                       addVar (type2llvmtype t) (Ident id)
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
  (BStmt (Block ss))                -> do modify $ \e' -> e' {vars=([]:vars e')}
                                          mapM_ stmtCode ss
                                          modify $ \e' -> e' {vars=tail(vars e')}
  Decl t is                         -> case is of
                                        [] -> return ()
                                        (NoInit id:is') -> do
                                           (VReg t' r) <- addVar (type2llvmtype t) id
                                           alloca r (Prim t)
                                           stmtCode (Decl t is')
                                        (Init id e:is') -> do
                                           v <- exprCode e
                                           var@(VReg t' r) <- addVar (type2llvmtype t) id
                                           alloca r (Prim t)
                                           store v var
                                           stmtCode (Decl t is')
  Ass id e@(TExp t e')      -> do r1 <- exprCode e
                                  var <- getVar id
                                  store r1 var
  Incr  id                          -> do var <- getVar id
                                          r1 <- load var
                                          r2 <- add  (VInt 1)  r1
                                          store r2 var
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
  While (TExp Bool ELitTrue) s      -> if returns [s] then stmtCode s
                                                      else return ()
  While (TExp Bool ELitFalse) _     -> return ()
  While expr stmt                   -> do begin <- getLabel
                                          loop  <- getLabel
                                          end   <- getLabel
                                          goto begin
                                          putLabel begin
                                          v <- exprCode expr
                                          comp <- cmp NE v (VBit 0)
                                          br comp loop end
                                          putLabel loop
                                          stmtCode stmt
                                          goto begin
                                          putLabel end
  ArrAss id [EDimen d] e@(TExp t _) -> do val <- exprCode e
                                          idx <- exprCode d
                                          vec <- getVar id
                                          setelem vec [idx] val
  ArrAss id ds e@(TExp t _)         -> do vec <- getVar id
                                          is  <- mapM (\(EDimen d) -> exprCode d) ds
                                          val <- exprCode e
                                          setelem vec is val
  For t id0 id1 s                   -> do counter <- newRegister >>= 
                                                     (\r -> alloca r (Prim Int) >> 
                                                            return (VReg (Ptr (Prim Int)) r))
                                          store (VInt 0) counter
                                          vector <- getVar id1
                                          len <- veclen vector []
                                          elem@(VReg _ r) <- addVar (type2llvmtype t) id0
                                          alloca r (Prim t)
                                          start <- getLabel
                                          loop  <- getLabel
                                          end   <- getLabel
                                          goto start
                                          putLabel start
                                          count <- load counter
                                          comp <- cmp LTH count len
                                          br comp loop end
                                          putLabel loop
                                          idx <- load counter
                                          r <- getelem vector [idx]
                                          store r elem
                                          stmtCode s
                                          v <- load elem
                                          setelem vector [idx] v
                                          r1 <- add (VInt 1) idx
                                          store r1 counter
                                          goto start
                                          putLabel end
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Generate code for expressions
--------------------------------------------------------------------------------
-- | Generate LLVM code for a Javalette expression. It will return a Value
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
                        putLabel false0
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
                          newvec len (Vector (Prim t)) >>= load
  EArr t' ds         -> do newmdvec ds (type2llvmtype t) >>= load
  EArrLen id        -> getVar id >>= (\t -> veclen t [])
--  EArrIdx id [EDimen d] -> do vec <- getVar id
--                              idx <- exprCode d
--                              getelem vec [idx]
  EArrIdx id ds -> do vec <- getVar id
                      ids <- mapM (\(EDimen d) -> exprCode d) ds
                      getelem vec ids
  EArrMDLen id ds -> do lens <- mapM (\(EDimen d) -> exprCode d) ds
                        vec <- getVar id
                        veclen vec lens
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
                         putCode [ show r ++ " = " ++ fun ++ " " ++ show t ++
                                   " " ++ unValue op1 ++ ", " ++ unValue op2]
                         return (VReg t r)

add :: Value -> Value -> Result Value
add op1 op2 = binOp op1 op2 op t
  where (op,t) = if isInts op1 op2 then ("add" , (Prim Int))
                                   else ("fadd", (Prim Doub))

sub :: Value -> Value -> Result Value
sub op1 op2 = binOp op1 op2 op t
  where (op,t) = if isInts op1 op2 then ("sub" , (Prim Int))
                                   else ("fsub", (Prim Doub))

mul' :: Value -> Value -> Result Value
mul' op1 op2 = binOp op1 op2 op t
  where (op,t) = if isInts op1 op2 then ("mul" , (Prim Int))
                                   else ("fmul", (Prim Doub))

div' :: Value -> Value -> Result Value
div' op1 op2 =  binOp op1 op2 op t
  where (op,t) = if isInts op1 op2 then ("sdiv", (Prim Int))
                                   else ("fdiv", (Prim Doub))

rem' :: Value -> Value -> Result Value
rem' op1 op2 = binOp op1 op2 op t
  where (op,t) = if isInts op1 op2 then ("srem", (Prim Int))
                                   else ("frem", (Prim Doub))

cmp :: RelOp -> Value -> Value -> Result Value
cmp op v1 v2 = do r <- newRegister
                  putCode [ show r ++ " = " ++ f ++ " " ++ op' ++ " "
                          , show v1 ++ ", " ++ unValue v2]
                  return (VReg (Prim Bool) r)
    where (t,f) = if isInts v1 v2 then (Int,"icmp") else (Doub,"fcmp")
          op' = case t of
                  Int  -> case op of EQU -> "eq";  NE  -> "ne";  LTH -> "slt"
                                     GTH -> "sgt"; LE  -> "sle"; GE  -> "sge"
                  Doub -> case op of EQU -> "oeq"; NE  -> "one"; LTH -> "olt"
                                     GTH -> "ogt"; LE  -> "ole"; GE  -> "oge"

call :: LLVMType -> Ident -> [Value] -> Result Value
call (Prim Void) (Ident id) vs = do putCode ["call void @" ++id++"("++f vs++")"]
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
                   putCode [show r0 ++ " = call i8* @calloc("++ show n ++ ", "++
                            show size ++ ")"]
                   return (VReg (Ptr I8) r0)

bitcast :: Value -> LLVMType -> Result Value
bitcast v t = do r <- newRegister
                 putCode [show r ++ " = bitcast " ++ show v ++ " to " ++ show t]
                 return (VReg t r)

setelem :: Value -> [Value] -> Value -> Result ()
setelem vec [] val = store val vec
setelem vec@(VReg (Ptr (Vector t)) _) (i:is) val = do
  vec0 <- getelementptr vec [VInt 0, VInt 1] >>= 
          (\r -> load (VReg (Ptr (Ptr t)) r ))
  elem <- getelementptr vec0 [i]
  setelem (VReg (Ptr t) elem) is val

getelem :: Value -> [Value] -> Result Value
getelem vec [] = load vec
getelem vec@(VReg (Ptr (Vector t)) _) (i:is) = do
  vec0 <- getelementptr vec [VInt 0, VInt 1] >>= 
          (\r -> load (VReg (Ptr (Ptr t)) r))
  elem <- getelementptr vec0 [i]
  getelem (VReg (Ptr t) elem) is

sizeof :: LLVMType -> Result Value
sizeof (Prim Int)  = return $ VInt 4
sizeof (Prim Doub) = return $ VInt 8
sizeof (Ptr _)     = return $ VInt 8
sizeof (Vector _)  = return $ VInt 16

newvec :: Value -> LLVMType -> Result Value
newvec len t@(Vector t0) = do
  vec <- newRegister
  let vector = (VReg (Ptr t) vec)
  alloca vec t
  sz <- sizeof t0
  xs0 <- calloc len sz
  xs1 <- bitcast xs0 (Ptr t0)
  r0 <- getelementptr vector [VInt 0, VInt 1]
  store xs1 (VReg (Ptr (Ptr t0)) r0)
  r1 <- getelementptr vector [VInt 0, VInt 0]
  store len (VReg (Ptr (Prim Int)) r1)
  return vector

newmdvec :: [ArrDimen] -> LLVMType -> Result Value
newmdvec blah@(EDimen d:ds) t@(Vector ts) = do
  len <- exprCode d
  vec <- newvec len t
  lens <- mapM (\(EDimen d) -> exprCode d) ds
  vecass len vec lens
  return vec

-- | This may need some commenting...
-- | vecass takes a 'mother' vector and allocates all its
-- | sub vectors.
vecass :: Value -> Value -> [Value] -> Result ()
vecass vlen vec [] = return ()
vecass vlen (vec@(VReg (Ptr (Vector t)) r)) (l:ls) = do
  start <- getLabel
  loop  <- getLabel
  end   <- getLabel
  count <- newRegister >>= (\r -> alloca r (Prim Int) >> 
                                  return (VReg (Ptr (Prim Int)) r))
  store (VInt 0) count
  goto start
  putLabel start
  idx <- load count
  comp <- cmp LTH idx vlen
  br comp loop end
  putLabel loop
  vec0 <- getelementptr vec [VInt 0, VInt 1] >>= 
          (\r -> load (VReg (Ptr (Ptr t)) r))
  elem <- getelementptr vec0 [idx] >>= (\r -> return (VReg (Ptr t) r))  
  elem_len <- getelementptr elem [VInt 0, VInt 0] >>= 
              (\r -> return (VReg (Ptr (Prim Int)) r))
  store l elem_len
  sz <- sizeof (f t)
  inner_vec <- calloc l sz >>= (\v -> bitcast v (Ptr (f t)))
  elem_vec <- getelementptr elem [VInt 0, VInt 1] >>= 
              (\r -> return (VReg (Ptr (Ptr (f t))) r))
  store inner_vec elem_vec
  vecass l elem ls
  next_idx <- add idx (VInt 1)
  store next_idx count
  goto start
  putLabel end
 where f (Vector (Prim t)) = Prim t
       f (Vector t) = t

veclen :: Value -> [Value] -> Result Value
veclen vec [] =  do l <- getelementptr vec [VInt 0, VInt 0]
                    load (VReg (Ptr (Prim Int)) l)
veclen vec@(VReg (Ptr (Vector t)) _) (i:is) = do
  vec0 <- getelementptr vec [VInt 0, VInt 1] >>= 
          (\r -> load (VReg (Ptr (Ptr t)) r))
  elem <- getelementptr vec0 [i]
  veclen (VReg (Ptr t) elem) is

getelementptr :: Value -> [Value] -> Result Register
getelementptr vec is = do r <- newRegister
                          putCode [show r ++ " = getelementptr inbounds "
                                  ,show vec ++ idx]
                          return r
    where idx = concat $ map (\v -> ", " ++ show v) is
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Utils.
--------------------------------------------------------------------------------
-- | Get the LLVM repr. of a Javalette type.
showType :: Type -> String
showType Int = "i32"
showType Doub = "double"
showType Void = "void"
showType Bool = "i1"
showType vec    = show $ type2llvmtype vec

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

type2llvmtype :: Type -> LLVMType
type2llvmtype (ArrInt [d])    = Vector (Prim Int)  
type2llvmtype (ArrInt (d:ds)) = Vector (type2llvmtype (ArrInt ds))
type2llvmtype (ArrDoub [d])    = Vector (Prim Doub)
type2llvmtype (ArrDoub (d:ds)) = Vector (type2llvmtype (ArrDoub ds))
type2llvmtype t = Prim t
--------------------------------------------------------------------------------
