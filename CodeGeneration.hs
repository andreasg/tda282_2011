module CodeGeneration (genCode) where

import AbsJavalette
import PrintJavalette
import ErrM
import Debug.Trace
import Data.List (nubBy)
import Data.Maybe (fromJust)
import Control.Monad.State

--------------------------------------------------------------------------------
-- Types, Data and Constants
--------------------------------------------------------------------------------
type Result a = StateT Scope Err a
data Scope = Scope { stackDepth    :: Int
                   , maxStackDepth :: Int
                   , vars          :: [[(Ident, Int)]]
                   , nextVar       :: Int
                   , label_count   :: Int
                   , code          :: [String]
                   , className     :: String }
           deriving Show

-- |Create a new scope
newScope ::  String -> Scope
newScope name = Scope 0 0 [[]] 0 0 [] name

-- | Substitute main with this name
javaletteMain :: String
javaletteMain = "javaletteMain"
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Generate code for toplevel definitions
--------------------------------------------------------------------------------
-- | Generates a string of Jasmin code from a Program
genCode :: Program -> String -> String
genCode (Program ts) name = unlines $ classHeader name ++ main name ++ map f (map addHeader (map (runTopDef name) ts))
        where f s = unlines (code s)


-- | Generates the function-header, stack size etc.
addHeader :: (Scope,TopDef) -> Scope
addHeader (s,FnDef t (Ident id) args _) = s { code = [".method public static " ++ id' ++
                                                       "(" ++ map typeToChar (map (\(Arg t id) -> t) args) ++ ")" ++
                                                       [typeToChar t]
                                                     , ".limit stack "  ++ show (maxStackDepth s)
                                                     , ".limit locals " ++ show (nextVar s)
                                                     ] ++ code s
                                            }
                                            where id' = if id == "main" then javaletteMain else id

-- | Generate a Jasmin class-header
classHeader :: String -> [String]
classHeader n = [".class public " ++ n,".super java/lang/Object"]

-- | Jasmin main function, this will call the Javalette main-function and return
main :: String ->[String]
main n = [".method public static main([Ljava/lang/String;)V"
         ,".limit stack 1"
         ,".limit locals 1"
         ,"invokestatic " ++ n ++ "/" ++ javaletteMain ++ "()I"
         ,"pop"
         ,"return"
         ,".end method\n"
         ]

runTopDef :: String -> TopDef -> (Scope,TopDef)
runTopDef name t = case runStateT (topDefCode t) (newScope name) of
                   Ok (s,_) ->  (s,t)

-- | Build the scope for a function
topDefCode :: TopDef -> Result Scope
topDefCode (FnDef t (Ident id) args (Block ss)) = 
  do mapM_ (\(Arg t id) -> do addVar t id) args
     mapM_ stmtCode ss
     putCode [".end method\n"]
     get
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- State modifiers
--------------------------------------------------------------------------------
-- |Get the numeric id for an identifier
lookupId :: Ident -> Result Int
lookupId id= do s <- get
                case dropWhile (==Nothing) (map (lookup id) (vars s)) of
                  [] -> fail "blh"
                  (Just i:_) -> return i
  

-- |Add code to the scope
putCode :: [String] -> Result ()
putCode ss = modify (\s -> s {code = (code s ++ ss)})


-- |Modify the stack-depth for the current scope
incStack :: Int -> Result ()
incStack n = modify (\s -> 
                         s { maxStackDepth = max (maxStackDepth s) (stackDepth s + n)
                           , stackDepth    = (stackDepth s) + n } )


-- |Add a variable to the scope, and assign it a numeric id.
addVar :: Type -> Ident -> Result ()
addVar t id = case t of 
                Int -> modify (\s -> s { vars = ((id,nextVar s): head (vars s)) : tail (vars s)
                                       , nextVar = nextVar s + 1})
                Doub -> modify (\s -> s { vars = ((id,nextVar s): head (vars s)) : tail (vars s)
                                        , nextVar = nextVar s + 2})
--------------------------------------------------------------------------------

    
--------------------------------------------------------------------------------
-- Statement Code Generations
--------------------------------------------------------------------------------
stmtCode :: Stmt -> Result ()
stmtCode stmt = 
 case stmt of
  Empty               -> return ()
  (BStmt (Block ss))  -> mapM_ stmtCode ss
  Decl t is           -> case is of 
                           [] -> return ()
                           (NoInit id:is') -> addVar t id >> stmtCode (Decl t is')
                           (Init id expr:is') -> 
                               do exprCode expr
                                  addVar t id
                                  case t of
                                    Int -> do i <- lookupId id
                                              istore i
                                              stmtCode (Decl t is')
                                    Doub -> do i <- lookupId id
                                               dstore i
                                               stmtCode (Decl t is')
  Ass id e@(TExp t _)-> lookupId id >>= (\i -> case t of
                                                Int  -> exprCode e >> istore i
                                                Doub -> exprCode e >> dstore i)
  Incr id             -> lookupId id >>= iinc
  Decr id             -> lookupId id >>= idec
  Ret e@(TExp t _)     -> do exprCode e 
                             case t of 
                              Int  -> iret
                              Doub -> dret
  VRet                -> ret
  Cond expr stmt      -> undefined
  CondElse expr s0 s1 -> undefined
  While expr stmt     -> undefined
  SExp e@(TExp t e')  -> exprCode e >> case t of -- not sure if this is correct...
                                        Int  -> ipop
                                        Doub -> dpop
                                        Bool -> ipop
                                        Void -> return ()
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Expression Code Generation
--------------------------------------------------------------------------------
-- |Generate code for an expression
exprCode :: Expr -> Result ()
exprCode (TExp t e) = 
 case e of
  EVar id      -> do i <- lookupId id; case t of
                                        Int  -> iload i
                                        Doub -> dload i
  ELitInt i    -> bipush i
  ELitDoub d   -> dpush d
  ELitTrue     -> bipush 1
  ELitFalse    -> bipush 0
  EApp (Ident "printString") [TExp _ (EString s)] -> printStream >> spush s  >> incStack (-1) >> println 'S'
  EApp (Ident "printInt") es    -> printStream >> mapM_ exprCode es >> mapM_ popExpr es >> println 'I'
  EApp (Ident "printDouble") es -> printStream >> mapM_ exprCode es >> mapM_ popExpr es >> println 'D'
  EApp (Ident id) es   -> 
      do mapM_ exprCode es
         mapM_ popExpr es
         invokestatic t id es
  EString s    -> spush s
  Neg exp      -> fail "exprCode:: Neg Expr: not implemented yet"
  Not exp      -> fail "exprCode:: Not Expr: not implemented yet"
  EMul e0 o e1 -> exprCode e0 >> exprCode e1 >>
                  case t of 
                    Int  -> imul
                    Doub -> dmul
  EAdd e0 o e1 -> exprCode e0 >> exprCode e1 >> 
                  case t of 
                    Int  -> iadd
                    Doub -> dadd
  ERel e0 o e1 -> case o of
                   LTH -> undefined --     iflt  <label>
                   LE  -> undefined --     ifle  <label>
                   GTH -> undefined --     ifgt  <label>
                   GE  -> undefined --     ifge  <label>
                   EQU -> undefined --     ifeq  <label>
                   NE  -> undefined --     ifne  <label>
  EAnd e0 e1   -> exprCode e0 >> exprCode e1 >> iand >> incStack (-1)
  EOr  e0 e1   -> exprCode e0 >> exprCode e1 >> ior  >> incStack (-1)
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Jasmin Instructions
--------------------------------------------------------------------------------
iload  n = putCode ["iload "  ++ (show n)] >> incStack 1
istore n = putCode ["istore " ++ (show n)] >> incStack (-1)
dload  n = putCode ["dload "  ++ (show n)] >> incStack 2
dstore n = putCode ["dstore " ++ (show n)] >> incStack (-2)
bipush n = putCode ["bipush " ++ (show n)] >> incStack 1
dpush  n = putCode ["ldc2_w " ++ (show n)] >> incStack 2
spush  s = putCode ["ldc "    ++ (show s)] >> incStack 1
imul     = putCode ["imul"] >> incStack (-1)
dmul     = putCode ["dmul"] >> incStack (-2)
iadd     = putCode ["iadd"] >> incStack (-1)
dadd     = putCode ["dadd"] >> incStack (-2)
ipop     = putCode ["pop"]  >> incStack (-1)
dpop     = putCode ["pop2"] >> incStack (-2)
iret     = putCode ["ireturn"]
dret     = putCode ["dreturn"]
ret      = putCode ["return"]
iinc n   = putCode ["iinc " ++ show n ++ " 1"]
idec n   = putCode ["iinc " ++ show n ++ " -1"]
iand      = putCode ["and"]
ior       = putCode ["or"]
printStream = putCode ["getstatic java/lang/System/out Ljava/io/PrintStream;"] >> incStack 1
println c = putCode ["invokevirtual java/io/PrintStream/println("++s++")V"]    >> incStack (-1)
  where s = case c of 'S' -> "Ljava/lang/String;"
                      'I' -> "I"
                      'D' -> "D"
invokestatic t id es = do s <- get
                          putCode ["invokestatic " ++ className s ++ "/" ++ id ++
                                   "(" ++ map exprToChar es ++ ")" ++ [typeToChar t]]
                          case t of Void -> return ()
                                    Int  -> incStack 1
                                    Doub -> incStack 2
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Util functions
--------------------------------------------------------------------------------
typeToChar :: Type -> Char
typeToChar t = fromJust $ lookup t [(Int,'I'),(Doub,'D'),(Void,'V')]
exprToChar (TExp t _) = typeToChar t

-- | Reduces the stack-counter by the amount of the type of the expression.
popExpr :: Expr -> Result ()
popExpr (TExp _ (EString _)) = incStack (-1)
popExpr (TExp t _) =
  case t of
    Int -> incStack (-1)
    Doub -> incStack (-2)
    Void -> return ()
--------------------------------------------------------------------------------
