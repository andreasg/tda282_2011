module TypeChecker (typecheck) where


-- BNF Converter imports
import AbsJavalette
import PrintJavalette
import ErrM

import Debug.Trace (putTraceMsg,trace)
import System.IO.Unsafe (unsafePerformIO)
import Data.List (nubBy)
import Control.Monad.Reader

import ReturnChecker


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


addVars :: Type -> [Item] -> Env -> Env
addVars t is (e:es) = (foldr (:) e (zip (map f is) (repeat t))):es
    where f (NoInit id) = id
          f (Init id _) = id


checkTopDef :: TopDef -> State TopDef
checkTopDef (FnDef t id args (Block b)) = 
  local (\x -> map (\(Arg t i) -> (i,t)) args : x) (typeStmt b t) >>= (\ss -> return $ FnDef t id args 
                                                                           (Block (if t == Void then ss++[VRet] else ss)))

typeStmt :: [Stmt] -> Type -> State [Stmt]
typeStmt []                   rt = return []
typeStmt (Empty:s)            rt = typeStmt s rt >>= return . (:) Empty
typeStmt (BStmt (Block b):s)  rt = local ((:)[]) (typeStmt b rt) >>= (\ss -> typeStmt s rt >>= 
                                                                             return . (:) (BStmt (Block ss)))
typeStmt (Incr id:s)          rt = inferNumId id >> (typeStmt s rt >>= return . (:) (Incr id))
typeStmt (Decr id:s)          rt = inferNumId id >> (typeStmt s rt >>= return . (:) (Decr id))
typeStmt (SExp e:s)           rt = typeExpr e >>= (\e' -> typeStmt s rt >>= return . (:) (SExp e'))
typeStmt (Decl Void _:s)      rt = fail "Cannot declare var with type Void."
typeStmt (Decl t is:s)        rt = do is' <- mapM (checkItem t) is
                                      ss  <- local (addVars t is') (typeStmt s rt)
                                      return $ Decl t is' : ss
typeStmt (Cond e s':s)        rt = do e'     <- inferBool e
                                      s'':[] <- local id (typeStmt [s'] rt)
                                      ss <- typeStmt s rt
                                      return $ Cond e' s'' : ss
typeStmt (CondElse e s0 s1:s) rt = do e' <- inferBool e
                                      [s0'] <- local id (typeStmt [s0] rt)
                                      [s1'] <- local id (typeStmt [s1] rt)
                                      typeStmt s rt >>= return . (:) (CondElse e' s0' s1')
typeStmt (While e s':s)       rt = do e' <- inferBool e
                                      [s''] <- local id (typeStmt [s'] rt)
                                      typeStmt s rt >>= return . (:) (While e' s'')
typeStmt (Ass id e:s)         rt = do (TExp t e') <- typeExpr e
                                      t' <- typeIdent id
                                      case t' of
                                        ArrInt  _ -> typeStmt (ArrAss id [] e:s) rt
                                        ArrDoub _ -> typeStmt (ArrAss id [] e:s) rt
                                        _         -> if t == t'
                                                      then typeStmt s rt >>= return . (:) (Ass id (TExp t e'))
                                                      else fail $ "Expression " ++ show e ++ " has the wrong type " ++ show t
typeStmt (Ret e:s)            rt = do local id (typeStmt s rt)
                                      (TExp t e') <- typeExpr e
                                      if t == rt
                                        then typeStmt s rt >>= return . (:) (Ret (TExp t e'))
                                        else fail $ show t ++ " is not of return type " ++ show rt
typeStmt (VRet:s)             rt | rt == Void = typeStmt s rt >>= return . (:) VRet
                                 | otherwise  = fail $ "Return type not " ++ show rt


typeStmt (ArrAss id ds0 expr0:s) rt=do t0   <- typeIdent id
                                       case t0 of
                                        ArrInt  ds -> f t0 ds
                                        ArrDoub ds -> f t0 ds
                                        _          -> fail "cannot do array assignment of non-array types."
  where f t0 ds = do ds0' <- mapM checkDimen ds0
                     expr0'@(TExp t1 expr1) <- typeExpr expr0
                     if length ds == length ds0
                       then if t1 == Int || t1 == Doub
                              then typeStmt s rt >>= return . (:) (ArrAss id ds0' expr0')
                              else fail "must assign int to element of int array "
                       else case expr1 of
                             (EArrIdx id1 ds1) -> do 
                                    ds1' <- mapM checkDimen ds1
                                    t1   <- typeIdent id1
                                    case t1 of
                                      ArrInt ds' -> if (length ds' - length ds1) ==
                                                    (length ds  - length ds0)
                                                     then typeStmt s rt >>= return . (:) (ArrAss id ds0' (TExp (ArrInt (arrDimen ds1')) (EArrIdx id1 ds1')))
                                                     else fail "array dimensions doesn't agree"
                                      _          -> fail "can only assign array to an array..."
                             e -> case t0 of
                                    ArrInt _ -> case t1 of
                                                  ArrInt _ -> typeStmt s rt >>= return . (:) (ArrAss id ds0' expr0')
                                                  _        -> fail "cannot assign array-ref of different type"
                                    ArrDoub _ -> case t1 of
                                                   ArrDoub _ -> typeStmt s rt >>= return . (:) (ArrAss id ds0' expr0')
                                                   _         -> fail "cannot assign array-ref of different type"
                                    _         -> fail "cannot assign array-ref of different type"


typeStmt (f@(For t i0 i1 _):ss) rt =local ((:)[(i0, t)]) (typeFor f) >>= (\s -> typeStmt ss rt >>=
                                                                          return . (:) (For t i0 i1 s))
    where typeFor :: Stmt -> State Stmt
          typeFor (For t i0 i1 s) = do t' <- typeIdent i1
                                       case t of 
                                        Void -> fail "invalid type in for"
                                        Bool -> fail "unsupported array type in for"
                                        Int  -> oneDimenFor t t' s
                                        Doub -> oneDimenFor t t' s
                                        ArrInt  ds -> mulDimenFor t t' s
                                        ArrDoub ds -> mulDimenFor t t' s
          oneDimenFor t t' s = case t' of
                                ArrInt  [e] -> if t == Int then do ss <- typeStmt [s] rt; return $ head ss
                                                           else fail "elem type does not mach array type in for"
                                ArrDoub [e] -> if t == Doub then do ss <- typeStmt [s] rt; return $ head ss 
                                                            else fail "elem type does not mach array type in for"
          mulDimenFor (ArrInt ds)  t' s = case t' of
                                            ArrInt ds'  -> if (length ds == (length ds')-1)
                                                            then do ss <- typeStmt [s] rt; return $ head ss
                                                            else fail "array dimension error in for"
                                            ArrDoub ds' -> fail "array types must agree in for"
          mulDimenFor (ArrDoub ds) t' s = case t' of
                                            ArrInt ds'  -> fail "array types must agree in for"
                                            ArrDoub ds' -> if (length ds == (length ds')-1)
                                                            then do ss <- typeStmt [s] rt; return $ head ss
                                                            else fail "array dimension error in for"


-- |Takes an expression and returns a type-annotated expression
typeExpr :: Expr -> State Expr
typeExpr (EVar id)         = typeIdent id >>= (\t -> return $ TExp t (EVar id))
typeExpr e@(ELitInt _)     = return $ TExp Int  e
typeExpr e@(ELitDoub _)    = return $ TExp Doub e
typeExpr ELitTrue          = return $ TExp Bool ELitTrue
typeExpr ELitFalse         = return $ TExp Bool ELitFalse
typeExpr e@(EString _)     = return $ TExp Void e
typeExpr (Neg e)           = inferNum e  >>= (\(TExp t e') -> return $ TExp t (Neg (TExp t e')))
typeExpr (Not e)           = inferBool e >>= (\(TExp t e') -> return $ TExp t (Not (TExp t e')))
typeExpr e@(EMul e0 op e1) = inferNumBin e0 e1  >>= (\(e'@(TExp t _),e'') -> return $ TExp t (EMul e' op e''))
typeExpr e@(EAdd e0 op e1) = inferNumBin e0 e1  >>= (\(e'@(TExp t _),e'') -> return $ TExp t (EAdd e' op e''))
typeExpr e@(EAnd e0 e1)    = inferBoolBin e0 e1 >>= (\(e,e') -> return $ TExp Bool (EAnd e e'))
typeExpr e@(EOr e0 e1)     = inferBoolBin e0 e1 >>= (\(e,e') -> return $ TExp Bool (EOr  e e'))
typeExpr e@(ERel e0 op e1) = do e0'@(TExp t0 _) <- typeExpr e0
                                e1'@(TExp t1 _) <- typeExpr e1
                                if t0 == t1
                                 then return (TExp Bool (ERel e0' op e1'))
                                 else fail "incompatable types in relop"
typeExpr e@(EApp id args)  = do argTs <- mapM typeExpr args
                                t'    <- typeIdent id
                                case t' of
                                  Fun t ts   -> if ts == [t | (TExp t _) <- argTs]
                                                 then return (TExp t (EApp id argTs))
                                                 else fail $ show id ++ " gets wrong arguments"
                                  _          -> fail $ show id ++ " does not exist"
typeExpr e@(EArrMDLen id ds) = do t <- typeIdent id
                                  ds' <- mapM checkDimen ds
                                  case t of
                                    ArrInt  d -> if length ds < length d then  return $ TExp Int (EArrMDLen id ds') 
                                                                         else fail msg
                                    ArrDoub d -> if length ds < length d then return $ TExp Int (EArrMDLen id ds')
                                                                         else fail msg
                                    _          -> fail ".length operator must be applied to array type"
       where msg = ".length must be applied to argument of type array"
typeExpr e@(EArrLen id)   = do t <- typeIdent id
                               case t of
                                 ArrInt  ds -> return $ TExp Int e
                                 ArrDoub ds -> return $ TExp Int e
                                 _          -> fail ".length operator must be applied to array type"
typeExpr e@(EArr t dim)  = do dim' <- mapM checkDimen dim
--                              e'' <- typeExpr e'
                              case t of 
                                Int  -> return $ TExp (ArrInt (arrDimen dim))  (EArr t dim')
                                Doub -> return $ TExp (ArrDoub (arrDimen dim)) (EArr t dim')
                                _    -> fail "invalid array type"
typeExpr e@(EArrIdx id ds) = do ds' <- mapM checkDimen ds
                                t   <- typeIdent id
                                case t of
                                  ArrInt  ds0 -> if length ds == length ds0 
                                                   then return $ TExp  Int (EArrIdx id ds')
                                                   else return $ TExp (ArrInt (take (length ds - length ds0) (repeat ArrItem))) (EArrIdx id ds')
                                  ArrDoub ds0 -> if length ds == length ds0
                                                   then return $ TExp Doub (EArrIdx id ds')
                                                   else return $ TExp (ArrDoub (take (length ds - length ds0) (repeat ArrItem))) (EArrIdx id ds')
                                  _           -> fail "cannot index non-array type"
typeExpr (TExp t e) = return (TExp t e)

                           
arrDimen :: [a] -> [ArrItem]
arrDimen xs = take (length xs) (repeat ArrItem)

checkDimen :: ArrDimen -> State ArrDimen
checkDimen (EDimen expr) = do (TExp t e) <- typeExpr expr
                              if t == Int
                                 then return (EDimen (TExp t e))
                                 else fail "checkDimen: array index must be of type int"


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


inferNumBin :: Expr -> Expr -> State (Expr,Expr)
inferNumBin e0 e1 = do
  e0'@(TExp t0 _) <- inferNum e0
  e1'@(TExp t1 _) <- inferNum e1
  if t0 == t1
    then return (e0',e1')
    else fail $ show e0 ++ " is not of the same type as " ++ show e1


inferNumId :: Ident -> State Type
inferNumId id = do
  t <- typeIdent id
  if elem t [Int]
    then return t
    else fail $ "Ident " ++ show id ++ " is not a integer"


inferBool :: Expr -> State Expr
inferBool e = do
  e'@(TExp t _) <- typeExpr e
  if t == Bool
    then return e'
    else fail $ "Expression " ++ show e ++ " is not a boolean"


inferBoolBin :: Expr -> Expr -> State (Expr, Expr)
inferBoolBin e0 e1 = do 
  e0' <- inferBool e0
  e1' <- inferBool e1
  return (e0',e1')


checkItem :: Type -> Item -> State Item
checkItem t (NoInit id) = do
  (c:cs) <- ask
  case lookup id c of
    Nothing -> return (NoInit id)
    _       -> fail $ "Variable " ++ show id ++ " already exists in scope"
checkItem t (Init id e) = do
  (c:cs) <- ask
  (TExp t' e')  <- typeExpr e
  case lookup id c of
    Nothing -> if t == t'
               then return (Init id (TExp t' e'))
               else fail $ "Expression " ++ show e ++ " has the wrong type"
    _       -> fail $ "Variable " ++ show id ++ " already exists"