module TypeChecker where


-- BNF Converter imports
import AbsJavalette
import AbsJavalette
import PrintJavalette
import ErrM

import Debug.Trace (putTraceMsg,trace)
import System.IO.Unsafe (unsafePerformIO)
import Data.List (nubBy)
import Control.Monad.Reader


-- Environment, pair each identifier with it's type
-- each list in the list functions as a scope.
type Env = [[(Ident,Type)]]
type State a = ReaderT Env Err a


stdEnv =[[(Ident "printInt",    Fun Void [Int])
         ,(Ident "printDouble", Fun Void [Doub])
         ,(Ident "readDouble",  Fun Doub [])
         ,(Ident "readInt",     Fun Int  [])
         ,(Ident "printString", Fun Void [Void])]]


typecheck :: Program -> Err Program
typecheck (Program fs) = do
  e0 <- runReaderT (buildSig fs) stdEnv
  topDefs <- runReaderT (mapM checkTopDef fs) e0
  if returnCheck fs
   then return (Program topDefs)
   else fail "all non-void functions must return"


buildSig :: [TopDef] -> State Env
buildSig []                     = ask
buildSig (FnDef t id args _:xs) = do
  cs <- ask
  if elem id (map fst (concat cs))
    then fail $ "Duplicate defenitions of " ++ show id
    else if length args == length (nubBy (==) args)
         then local (\(x:xs) -> ((id,Fun t (map (\(Arg t i) -> t) args)):x):xs) (buildSig xs)
         else fail "Duplicate assignments of arguments"


-- use sequence here...?
addVars :: Type -> [Ident] -> Env -> Env
addVars t is (e:es) = (foldr (:) e (zip is (repeat t))):es


checkTopDef :: TopDef -> State TopDef
checkTopDef (FnDef t id args (Block b)) = 
  local (\x -> map (\(Arg t i) -> (i,t)) args : x) (typeStmt b t) >>= (\ss -> return $ FnDef t id args (Block ss))


typeStmt :: [Stmt] -> Type -> State [Stmt]
typeStmt []                   rt = return []
typeStmt (Empty:s)            rt = typeStmt s rt >>= (\ss -> return $ Empty:ss)
typeStmt (BStmt (Block b):s)  rt = local ((:)[]) (typeStmt b rt) >>= (\ss -> typeStmt s rt >>= 
                                                                     (\ss' -> return $ (BStmt (Block ss)) :ss'))
typeStmt (Incr id:s)          rt = inferNumId id >> (typeStmt s rt >>= (\ss -> return $ Incr id:ss))
typeStmt (Decr id:s)          rt = inferNumId id >> (typeStmt s rt >>= (\ss -> return $ Decr id:ss))
typeStmt (SExp e:s)           rt = typeExpr e >>= (\e' -> typeStmt s rt >>= (\ss -> return $ SExp e':ss))
typeStmt (Decl Void _:s)      rt = fail "Cannot declare void var."
typeStmt (Decl t is:s)        rt = do ids <- mapM (checkItem t) is
                                      ss  <- local (addVars t ids) (typeStmt s rt)
                                      return $ Decl t is : ss
typeStmt (Cond e s':s)        rt = do e'     <- inferBool e
                                      s'':[] <- local id (typeStmt [s'] rt)
                                      ss <- typeStmt s rt
                                      return $ Cond e' s'' : ss
typeStmt (CondElse e s0 s1:s) rt = do e' <- inferBool e
                                      s0':[] <- local id (typeStmt [s0] rt)
                                      s1':[] <- local id (typeStmt [s1] rt)
                                      ss <- typeStmt s rt
                                      return $ CondElse e' s0' s1' : ss
typeStmt (While e s':s)       rt = do e' <- inferBool e
                                      s'':[] <- local id (typeStmt [s'] rt)
                                      typeStmt s rt >>= (\ss -> return $ While e' s'' : ss)
typeStmt (Ass id e:s)         rt = do (TExp t e') <- typeExpr e
                                      t' <- typeIdent id
                                      if t == t'
                                         then typeStmt s rt >>= (\ss -> return $ Ass id (TExp t e') : ss)
                                         else fail $ "Expression " ++ show e
                                                                   ++ " has the wrong type"
typeStmt (Ret e:s)            rt = do local id (typeStmt s rt)
                                      (TExp t e') <- typeExpr e
                                      if t == rt
                                        then typeStmt s rt >>= (\ss -> return $ Ret (TExp t e') : ss)
                                        else fail $ show t ++ " is not of return type " ++ show rt
typeStmt (VRet:s)             rt | rt == Void = typeStmt s rt >>= (\ss -> return $ VRet : ss)
                                 | otherwise  = fail $ "Return type not " ++ show rt


typeExpr :: Expr -> State Expr
typeExpr (EVar id)         = typeIdent id >>= (\t -> return $ TExp t (EVar id))
typeExpr e@(ELitInt _)     = return $ TExp Int  e
typeExpr e@(ELitDoub _)    = return $ TExp Doub e
typeExpr ELitTrue          = return $ TExp Bool ELitTrue
typeExpr ELitFalse         = return $ TExp Bool ELitFalse
typeExpr e@(EString _)     = return $ TExp Void e
typeExpr (Neg e)           = inferNum e  >>= (\(TExp t e') -> return $ TExp t (Neg (TExp t e')))
typeExpr (Not e)           = inferBool e >>= (\(TExp t e') -> return $ TExp t (Not (TExp t e')))

typeExpr e@(EMul e0 op e1)  = inferNumBin e0 e1  >>= (\(e'@(TExp t _),e'') -> return $ TExp t (EMul e' op e''))
typeExpr e@(EAdd e0 op e1)  = inferNumBin e0 e1  >>= (\(e'@(TExp t _),e'') -> return $ TExp t (EAdd e' op e''))


--typeExpr e@(EAdd e0 _ e1)  = inferNumBin e0 e1  >>= (\t -> return $ TExp t e)
typeExpr e@(EAnd e0 e1)    = inferBoolBin e0 e1 >>= (\(e,e') -> return $ TExp Bool (EAnd e e'))
typeExpr e@(EOr e0 e1)     = inferBoolBin e0 e1 >>= (\(e,e') -> return $ TExp Bool (EOr  e e'))
typeExpr e@(ERel e0 op e1) = do e0'@(TExp t0 _) <- typeExpr e0
                                e1'@(TExp t1 _) <- typeExpr e1
                                if t0 == t1
                                 then return (TExp Bool (ERel e0' op e1'))
                                 else fail "incompatable types in relop"
typeExpr e@(EApp id args)  = do argTs <- mapM typeExpr args
                                t' <- typeIdent id
                                case t' of
                                  Fun t ts   -> if ts == [t | (TExp t _) <- argTs]
                                                 then return (TExp t e)
                                                 else fail $ show id ++ " gets wrong arguments"
                                  _          -> fail $ show id ++ " does not exist"


typeIdent :: Ident -> State Type
typeIdent id = do
  cs <- ask
  case dropWhile (==Nothing) (map (lookup id) cs) of
    []     -> fail $ "No such variable: " ++ show id
    (Just t:ts) -> return t


inferNum :: Expr -> State Expr
inferNum e = do
  (TExp t e') <- typeExpr e
  if elem t [Int,Doub]
    then return (TExp t e')
    else fail $ "Expression " ++ show e ++ " is not a numeral"


inferNumId :: Ident -> State Type
inferNumId id = do
  t <- typeIdent id
  if elem t [Int,Doub]
    then return t
    else fail $ "Ident " ++ show id ++ " is not a numeral"


inferNumBin :: Expr -> Expr -> State (Expr,Expr)
inferNumBin e0 e1 = do
  e0'@(TExp t0 _) <- inferNum e0
  e1'@(TExp t1 _) <- inferNum e1
  if t0 == t1
    then return (e0',e1')
    else fail $ show e0 ++ " is not of the same type as " ++ show e1


inferBool :: Expr -> State Expr
inferBool e = do
  e'@(TExp t _) <- typeExpr e
  if t == Bool
    then return e'
    else fail $ "Expression " ++ show e ++ " is not a boolean"


inferBoolBin :: Expr -> Expr -> State (Expr, Expr)
inferBoolBin e0 e1 = do e0' <- inferBool e0
                        e1' <- inferBool e1
                        return (e0',e1')


checkItem :: Type -> Item -> State Ident
checkItem _ (NoInit id) = do
  (c:cs) <- ask
  case lookup id c of
    Nothing -> return id
    _       -> fail $ "Variable " ++ show id ++ " already exists in scope"
checkItem t (Init id e) = do
  (c:cs) <- ask
  (TExp t' e')  <- typeExpr e
  case lookup id c of
    Nothing -> if t == t'
               then return id
               else fail $ "Expression " ++ show e ++ " has the wrong type"
    _       -> fail $ "Variable " ++ show id ++ " already exists"


-- check if a program returns correctly
returnCheck :: [TopDef] -> Bool
returnCheck fs = not $ elem False (map (\(FnDef _ _ _ (Block stms)) -> returns stms) fs')
    where fs' = filter (\(FnDef t _ _ _) -> t /= Void) fs -- filter non-void funs
          returns :: [Stmt] -> Bool
          returns []                              = False
          returns (Ret _:_)                       = True
          returns (BStmt (Block stms):xs)         = returns stms || returns xs
          returns (CondElse ELitTrue s1 _  : ss)  = returns [s1] || returns ss
          returns (CondElse ELitFalse _ s2 : ss)  = returns [s2] || returns ss
          returns (CondElse _ s1 s2 : ss)         = (returns [s1] && returns [s2]) || returns ss
          returns (Cond ELitTrue s1:ss)           = returns [s1] || returns ss
          returns (Cond ELitFalse _:ss)           = returns ss
          returns (While ELitTrue s : ss)         = returns [s] || returns ss
          returns (_:ss)                          = returns ss