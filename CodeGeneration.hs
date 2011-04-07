module CodeGeneration (testGenCode) where

import AbsJavalette
import PrintJavalette
import ErrM
import Debug.Trace
import Data.List (nubBy)
import Data.Maybe (fromJust)
import Control.Monad.State
--import TypeChecker

--------------------------------------------------------------------------------
-- Types and Data
--------------------------------------------------------------------------------
type Result a = StateT Scope Err a
data Scope = Scope { stackDepth    :: Int
                   , maxStackDepth :: Int
                   , vars          :: [(Ident, Int)]
                   , nextVar       :: Int
                   , label_count   :: Int
                   , code          :: [String]
                   , className     :: String }
           deriving Show




testGenCode :: Program -> String -> IO ()
testGenCode (Program topDefs) name = 
    case runStateT (mapM topDefCode topDefs) (newScope name) of
      Ok (_,scope) -> putStrLn (unlines (code scope))
      _            -> putStrLn "code gen fail"




              
                 


-- |Create a new scope
newScope ::  String -> Scope
newScope name = Scope 0 0 [] 0 0 [] name


-- instructions
iload  n = "iload_" ++ (show n)
istore n = "istore_" ++ (show n)
dload  n = "dload_" ++ (show n)
dstore  n = "dstore_" ++ (show n)
bipush n = "bipush " ++ (show n)
ldc_w  n = "ldc_w "  ++ (show n)


-- |Get the numeric id for an identifier
lookupId :: Ident -> Result Int
lookupId id = do s <- get
                 case lookup id (vars s) of
                   Just i -> return i
                   Nothing -> fail "lookupId :: Ident not found in scope"
  

-- |Add code to the scope
putCode :: [String] -> Result ()
putCode ss = modify (\s -> s {code = (code s ++ ss)})


-- |Modify the stack-depth for the current scope
incStack :: Int -> Result ()
incStack n = modify (\s -> 
                         s { maxStackDepth = max (maxStackDepth s) (maxStackDepth s + n)
                           , stackDepth    = (stackDepth s) + n } )

typeToChar :: Type -> Char
typeToChar t = fromJust $ lookup t [(Int,'I'),(Doub,'D'),(Void,'V')]
exprToChar (TExp t _) = typeToChar t


addVar :: Type -> Ident -> Result ()
addVar t id = case t of 
                Int -> modify (\s -> s { vars = ((id,nextVar s - 1):vars s)
                                       , nextVar = nextVar s + 1})
                Doub -> modify (\s -> s { vars = ((id,nextVar s - 2):vars s)
                                        , nextVar = nextVar s + 2})

-- generate code for a function
topDefCode :: TopDef -> Result ()
topDefCode (FnDef t (Ident id) args (Block ss)) = 
  do
    putCode [".method public static " ++ id ++ 
             "(" ++ map typeToChar (map (\(Arg t id) -> t) args) ++ ")" ++
             [typeToChar t]]
    putCode [".limit stack 100"]
    putCode [".limit locals 100"]     

    mapM_ (\(Arg t id) -> do addVar t id) args

    mapM_ stmtCode ss
    putCode [".end method\n"]
    

-- generate code for a statement
stmtCode :: Stmt -> Result ()
stmtCode stmt = 
 case stmt of
  Empty               -> putCode ["nop"]
  (BStmt (Block ss))  -> mapM_ stmtCode ss -- add all parameter vars to the var-list
  Decl t is           -> case is of 
                           [] -> return ()
                           (NoInit id:is') -> addVar t id >> stmtCode (Decl t is')
                           (Init id expr:is') -> 
                               do addVar t id
                                  exprCode expr
                                  case t of
                                    Int -> do i <- lookupId id
                                              putCode[istore i]
                                              stmtCode (Decl t is')
                                    Doub -> do i <- lookupId id
                                               putCode[dstore i]
                                               stmtCode (Decl t is')
  Ass id e@(TExp t _)-> lookupId id >>= (\i -> case t of
                                                Int -> exprCode e >> putCode [istore i]
                                                Doub -> exprCode e >> putCode [dstore i])
  Incr id             -> undefined
  Decr id             -> undefined
  Ret e@(TExp t _)     -> do exprCode e 
                             case t of 
                              Int  -> putCode["ireturn"]
                              Doub -> putCode["dreturn"]
  VRet                -> putCode ["return"]
  Cond expr stmt      -> undefined
  CondElse expr s0 s1 -> undefined
  While expr stmt     -> undefined
  SExp e              -> exprCode e -- right??

-- |Generate code for an expression
exprCode :: Expr -> Result ()
exprCode (ELitInt i) = putCode [bipush i]
exprCode (ELitDoub d) = putCode [ldc_w d]
exprCode (TExp t e) = 
 case e of
  EVar id      -> do i <- lookupId id -- bug here?
                     case t of
                       Int  -> putCode [iload i] >> incStack 1
                       Doub -> putCode [dload i]
  ELitInt i    -> putCode [bipush i] >> incStack 1
  ELitDoub d   -> putCode [ldc_w d]  >> incStack 1
  ELitTrue     -> putCode [bipush 1] >> incStack 1
  ELitFalse    -> putCode [bipush 0] >> incStack 1
  EApp (Ident id) es   -> 
      do mapM_ exprCode es
         s <- get
         putCode ["invokestatic " ++ className s ++ "/" ++ id ++
                 "(" ++ map exprToChar es ++ ")" ++ [typeToChar t]] >> if t == Void
                                                                        then incStack 0
                                                                        else incStack 1
  EString s    -> putCode ["ldc_w "++s]  >> incStack 1
  Neg exp      -> fail "exprCode:: Neg Expr: not implemented yet"
  Not exp      -> fail "exprCode:: Not Expr: not implemented yet"
  EMul e0 o e1 -> exprCode e0 >> exprCode e1 >>
                  case t of 
                    Int  -> putCode ["imul"] >> incStack 1
                    Doub -> putCode ["dmul"] >> incStack 1
  EAdd e0 o e1 -> exprCode e0 >> exprCode e1 >> 
                  case t of 
                    Int  -> putCode["iadd"] >> incStack (-1)
                    Doub -> putCode["dadd"] >> incStack (-1)
  ERel e0 o e1 -> fail "exprCode:: ERel Expr Op Expr: not implemented yet"
  EAnd e0 e1   -> exprCode e0 >> exprCode e1 >> putCode ["and"] >> incStack (-1)
  EOr  e0 e1   -> fail "exprCode:: EOr Expr Expr: not implemented yet"



--------------------------------------------------------------------------------
-- Test Functions
--------------------------------------------------------------------------------
testExpr :: [Expr] -> IO ()
testExpr es = case runStateT (mapM_ exprCode es) (newScope "ClassName") of
                  Ok c -> putStrLn $ (unlines (code (snd c)) ++ "maxStackDepth = " ++ 
                                      (show ( maxStackDepth (snd c))))
                  _    -> putStrLn "testExpr fail"


-- Test xpression
eAddTest = [TExp Int (EAdd (TExp Int (ELitInt 10)) Plus (TExp Int (ELitInt 20)))]


-- 10 + 20;
-- f(10, 2.0)
eAppTest = [TExp Int (EAdd (TExp Int (ELitInt 10)) Plus (TExp Int (ELitInt 20)))
           ,TExp Int (EApp (Ident "f") [TExp Int (ELitInt 10)
                                       ,TExp Doub (ELitDoub 2.0)
                                       ])]