module TypeChecker where

import Control.Monad.Reader

import Debug.Trace

import AbsJavalette
import AbsJavalette
import PrintJavalette
import ErrM
import Data.List (nubBy)

type Env = [(Ident,Type)]

type State a = ReaderT Env Err a

testP = Program [FnDef Int (Ident "main") [] (Block [SExp (EApp (Ident "printInt") [ELitDoub 1.0]),Ret (ELitInt 0)])]
testProg :: Program
testProg = Program [FnDef Int (Ident "fun0") [Arg Doub (Ident "x")
                                       ,Arg Doub (Ident "y")] (Block [Empty])
                   ,FnDef Doub (Ident "fun1") [] (Block [Empty])]

stdEnv = [(Ident "printInt",    Fun Void [Int]),
          (Ident "printDouble", Fun Void [Doub]),
          (Ident "readDouble",  Fun Doub []),
          (Ident "readInt",     Fun Int []),
          (Ident "printString", Fun Void [Void])]

typecheck :: Program -> Err Env
typecheck (Program fs) =  do 
  env <- runReaderT (buildSig fs) stdEnv
  runReaderT (typeCheck' fs) env
  



typeCheck' :: [TopDef] -> State Env
typeCheck' fs = do mapM_ checkTopDef fs
                   ask

buildSig :: [TopDef] -> State Env
buildSig []                     = ask
buildSig (FnDef t id args _:xs) = do
  cs <- ask  
  if elem id (map fst cs)
    then fail $ "Duplicate defenitions of " ++ show id
    else if length args == length (nubBy (==) args)
         then local (\x -> (id,Fun t (map (\(Arg t i) -> t) args)):x) (buildSig xs)
         else fail "Duplicate assignments of arguments"


checkTopDef :: TopDef -> State Type
checkTopDef (FnDef t id args (Block b)) = 
  local (\x -> map f args ++ x) (typeStmt b t)
    where f (Arg t i) = (i,t)


typeStmt :: [Stmt] -> Type -> State Type
typeStmt []                   rt = return Void
typeStmt (Empty:s)            rt = typeStmt s rt
typeStmt (BStmt (Block b):s)  rt = do
  local id (typeStmt b rt)
  typeStmt s rt
typeStmt (Decl t is:s)        rt = do
  ids <- mapM (checkItem t) is
  local (addVars t ids) (typeStmt s rt)
typeStmt (Ass id e:s)         rt = do
  t <- typeExpr e
  cs <- ask
  case lookup id cs of
    Nothing -> fail $ "Variable " ++ show id ++ " does not exist"
    Just t' -> if t'==t
               then typeStmt s rt
               else fail $ "Expression " ++ show e ++ " has the wrong type"
typeStmt (Incr id:s)          rt = do
  inferNumId id
  typeStmt s rt
typeStmt (Decr id:s)          rt = do
  inferNumId id
  typeStmt s rt
typeStmt (Ret e:s)            rt = do
  local id (typeStmt s rt)
  t <- typeExpr e
  if t == rt
    then return t
    else fail $ show t ++ " is not of return type " ++ show rt
typeStmt (VRet:s)             rt | rt == Void = return Void
                                 | otherwise  = fail $ "Return type not " ++ show rt
typeStmt (Cond e s':s)        rt = do
  inferBool e
  local id (typeStmt [s'] rt)
  typeStmt s rt
typeStmt (CondElse e s0 s1:s) rt = do
  inferBool e
  local id (typeStmt [s0] rt)
  local id (typeStmt [s1] rt)
  typeStmt s rt
typeStmt (While e s':s)       rt = do
  inferBool e
  local id (typeStmt [s'] rt)
  typeStmt s rt
typeStmt (SExp e:s)           rt = do
  typeExpr e
  typeStmt s rt


typeExpr :: Expr -> State Type
typeExpr (EVar id)      = typeIdent id
typeExpr (ELitInt _)    = return Int
typeExpr (ELitDoub _)   = return Doub
typeExpr ELitTrue       = return Bool
typeExpr ELitFalse      = return Bool
typeExpr (EString _)    = return Void
typeExpr (Neg e)        = inferNum e
typeExpr (Not e)        = inferBool e
typeExpr (EMul e0 _ e1) = inferNumBin e0 e1
typeExpr (EAdd e0 _ e1) = inferNumBin e0 e1
typeExpr (ERel e0 op e1) = do
  t0 <- typeExpr e0
  t1 <- typeExpr e1
  if t0 == t1
    then return Bool
    else fail "incompatable types in relop"
typeExpr (EAnd e0 e1)   = inferBoolBin e0 e1
typeExpr (EOr e0 e1)    = inferBoolBin e0 e1
typeExpr (EApp id args) = do
  cs <- ask
  argTs <- mapM typeExpr args
  case lookup id cs of
    Just (Fun t ts) -> if ts == argTs
                       then return t
                       else fail $ show id ++ " gets wrong arguments"
    _               -> fail $ show id ++ " does not exist"



addVars :: Type -> [Ident] -> Env -> Env
addVars t is e = foldr (:) e (zip is (repeat t))

checkItem :: Type -> Item -> State Ident
checkItem _ (NoInit id) = do
  cs <- ask
  case lookup id cs of
    Nothing -> return id
    _       -> fail $ "Variable " ++ show id ++ " already exists"
checkItem t (Init id e) = do
  cs <- ask
  t' <- typeExpr e
  case lookup id cs of
    Nothing -> if t == t'
               then return id
               else fail $ "Expression " ++ show e ++ " has the wrong type"
    _       -> fail $ "Variable " ++ show id ++ " already exists"

typeIdent :: Ident -> State Type
typeIdent id = do
  cs <- ask
  case lookup id cs of
    Nothing -> fail $ "No such variable: " ++ show id
    Just t  -> return t

inferNum :: Expr -> State Type
inferNum e = do
  t <- typeExpr e
  if elem t [Int,Doub]
    then return t
    else fail $ "Expression " ++ show e ++ " is not a numeral"

inferNumId :: Ident -> State Type
inferNumId id = do
  t <- typeIdent id
  if elem t [Int,Doub]
    then return t
    else fail $ "Ident " ++ show id ++ " is not a numeral"


inferNumBin :: Expr -> Expr -> State Type
inferNumBin e0 e1 = do
  t0 <- inferNum e0
  t1 <- inferNum e1
  if t0 == t1
    then return t0
    else fail $ show e0 ++ " is not of the same type as " ++ show e1

inferBool :: Expr -> State Type
inferBool e = do
  t <- typeExpr e
  if t == Bool
    then return Bool
    else fail $ "Expression " ++ show e ++ " is not a boolean"

inferBoolBin :: Expr -> Expr -> State Type
inferBoolBin e0 e1 = do
  inferBool e0
  inferBool e1