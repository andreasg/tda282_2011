module TypeChecker where

-- BNF Converter imports
import AbsJavalette
import AbsJavalette
import PrintJavalette
import ErrM

import Debug.Trace
import Data.List (nubBy)
import Control.Monad.Reader


-- Environment, pair each identifier with it's type
type Env = [(Ident,Type)]
type State a = ReaderT Env Err a

-- Standard Environment, containing all 'std' functions of Javalette
stdEnv = [(Ident "printInt",    Fun Void [Int])
         ,(Ident "printDouble", Fun Void [Doub])
         ,(Ident "readDouble",  Fun Doub [])
         ,(Ident "readInt",     Fun Int [])
         ,(Ident "printString", Fun Void [Void])]


-- Check if a program is type correct
typecheck :: Program -> Err Bool
typecheck (Program fs) = runReaderT (buildSig fs) stdEnv  >>= 
                         runReaderT (mapM checkTopDef fs) >> 
                         if returnCheck fs 
                           then return True 
                           else fail "all non-void must return"

-- build type-signatures for functions
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
checkTopDef (FnDef t id args (Block b)) = local (\x -> map f args++x) (typeStmt b t)
    where f (Arg t i) = (i,t)


typeStmt :: [Stmt] -> Type -> State Type
typeStmt []                   rt = return Void
typeStmt (Empty:s)            rt = typeStmt s rt
typeStmt (BStmt (Block b):s)  rt = local id (typeStmt b rt) >> typeStmt s rt
typeStmt (Incr id:s)          rt = inferNumId id >> typeStmt s rt
typeStmt (Decr id:s)          rt = inferNumId id >> typeStmt s rt
typeStmt (SExp e:s)           rt = typeExpr e    >> typeStmt s rt
typeStmt (Decl t is:s)        rt = do ids <- mapM (checkItem t) is 
                                      local (addVars t ids) (typeStmt s rt)
typeStmt (Cond e s':s)        rt = do inferBool e
                                      local id (typeStmt [s'] rt)
                                      typeStmt s rt
typeStmt (CondElse e s0 s1:s) rt = do inferBool e
                                      local id (typeStmt [s0] rt)
                                      local id (typeStmt [s1] rt)         
                                      typeStmt s rt
typeStmt (While e s':s)       rt = do inferBool e
                                      local id (typeStmt [s'] rt)
                                      typeStmt s rt
typeStmt (Ass id e:s)         rt = do t <- typeExpr e
                                      cs <- ask
                                      case lookup id cs of
                                       Nothing -> fail $ "Variable " ++ show id ++ " does not exist"
                                       Just t' -> if t'==t
                                                   then typeStmt s rt
                                                   else fail $ "Expression " ++ show e 
                                                                             ++ " has the wrong type"
typeStmt (Ret e:s)            rt = do local id (typeStmt s rt)
                                      t <- typeExpr e
                                      if t == rt
                                        then return t
                                        else fail $ show t ++ " is not of return type " ++ show rt
typeStmt (VRet:s)             rt | rt == Void = return Void
                                 | otherwise  = fail $ "Return type not " ++ show rt


typeExpr :: Expr -> State Type
typeExpr (EVar id)       = typeIdent id
typeExpr (ELitInt _)     = return Int
typeExpr (ELitDoub _)    = return Doub
typeExpr ELitTrue        = return Bool
typeExpr ELitFalse       = return Bool
typeExpr (EString _)     = return Void
typeExpr (Neg e)         = inferNum e
typeExpr (Not e)         = inferBool e
typeExpr (EMul e0 _ e1)  = inferNumBin e0 e1
typeExpr (EAdd e0 _ e1)  = inferNumBin e0 e1
typeExpr (EAnd e0 e1)    = inferBoolBin e0 e1
typeExpr (EOr e0 e1)     = inferBoolBin e0 e1
typeExpr (ERel e0 op e1) = do t0 <- typeExpr e0
                              t1 <- typeExpr e1
                              if t0 == t1
                                then return Bool
                                else fail "incompatable types in relop"
typeExpr (EApp id args) = do cs <- ask
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
inferBoolBin e0 e1 = inferBool e0 >> inferBool e1

-- check if a program returns correctly
returnCheck :: [TopDef] -> Bool
returnCheck fs = not $ elem False (map (\(FnDef _ _ _ (Block stms)) -> returns stms) fs')
    where fs' = filter (\(FnDef t _ _ _) -> t /= Void) fs -- filter non-void funs
          returns :: [Stmt] -> Bool
          returns []                              = False
          returns (Ret _:_)                       = True
          returns (BStmt (Block stms):xs)         = returns stms || returns xs
          returns (CondElse ELitTrue s1 s2 : ss)  = returns [s1] || returns ss
          returns (CondElse ELitFalse s1 s2 : ss) = returns [s2] || returns ss
          returns (CondElse _ s1 s2 : ss)         = (returns [s1] && returns [s2]) || returns ss
          returns (Cond ELitTrue s1:ss)           = returns [s1] || returns ss
          returns (Cond ELitFalse _:ss)           = returns ss
          returns (While ELitTrue s : ss)         = returns [s] || returns ss
          returns (_:ss)                          = returns ss