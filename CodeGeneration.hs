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
-- | The state environment.
type Result a = State Scope a

-- | A scope is the 'container' for the code of a topdef. So, every topdef in
-- | a Javalette program is evaluated with it's own scope.
data Scope = Scope { stackDepth    :: Int              -- current stack depth
                   , maxStackDepth :: Int              -- maximum stack depth yet
                   , vars          :: [[(Ident, Int)]] -- variables in the scope
                   , nextVar       :: Int              -- next number to give var
                   , label_count   :: Int              -- label count
                   , code          :: [String]         -- the Jasmin code
                   , className     :: String }         -- name of the java class
           deriving Show


-- |Create a new scope, the name should be the Id of the java class
newScope ::  String -> Scope
newScope name = Scope 0 0 [[]] 0 0 [] name


-- | Substitute the Javalette main with this name, so as to avoid conflict with
-- | Java's main.
javaletteMain :: String
javaletteMain = "javaletteMain"
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Generate code for toplevel definitions
--------------------------------------------------------------------------------
-- | Generates a string of Jasmin code from a Program
genCode :: Program -> String -> String
genCode (Program ts) name =
  unlines $ classHeader name ++ main name ++ 
            map f (map addHeader (map (runTopDef name) ts))
        where f s = unlines (code s)


-- | Generates the function-header, stack size etc.
addHeader :: (Scope,TopDef) -> Scope
addHeader (s,FnDef t (Ident id) args _) =
  s { code = [".method public static " ++ id' ++
                "(" ++ map typeToChar (map (\(Arg t id) -> t) args) ++ ")" ++
                [typeToChar t]
             , ".limit stack "  ++ show (maxStackDepth s)
             , ".limit locals " ++ show (nextVar s)
             ] ++ code s }
             where id' = if id == "main" then javaletteMain else id


-- | Generate a Jasmin class-header
classHeader :: String -> [String]
classHeader n = [".class public " ++ n,".super java/lang/Object\n"]


-- | Jasmin main function, this will call the Javalette 
-- | main-function and then return.
main :: String ->[String]
main n = [".method public static main([Ljava/lang/String;)V"
         ,".limit stack 1"
         ,".limit locals 1"
         ,"\tinvokestatic " ++ n ++ "/" ++ javaletteMain ++ "()I"
         ,"\tpop"
         ,"\treturn"
         ,".end method\n\n"
         ]


-- | Generate code for a TopDef, returns the computed scope and the TopDef
runTopDef :: String -> TopDef -> (Scope,TopDef)
runTopDef name t = case runState (topDefCode t) (newScope name) of
                    (s,_) ->  (s,t)


-- | Build the scope for a function
topDefCode :: TopDef -> Result Scope
topDefCode (FnDef t (Ident id) args (Block ss)) =
  do mapM_ (\(Arg t id) -> do addVar t id) args
     mapM_ stmtCode ss
     putCode [".end method\n"]
     get
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- State modifiers and accessors
--------------------------------------------------------------------------------
-- |Get the numeric id for an identifier
lookupId :: Ident -> Result Int
lookupId id= do s <- get
                case dropWhile (==Nothing) (map (lookup id) (vars s)) of
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
addVar t id = 
 case t of
  Int  -> modify (\s -> s { vars = ((id,nextVar s):head (vars s)):tail (vars s)
                          , nextVar = nextVar s + 1})
  Doub -> modify (\s -> s { vars = ((id,nextVar s):head (vars s)):tail (vars s)
                          , nextVar = nextVar s + 2})

-- |Get the next label
getLabel :: Result String
getLabel = do s <- get
              modify (\s -> s {label_count = label_count s + 1})
              return ("L" ++ show (label_count s))
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Statement Code Generations
--------------------------------------------------------------------------------
-- | Generate Jasmin code for a Javalette Statement
stmtCode :: Stmt -> Result ()
stmtCode stmt =
 case stmt of
  Empty               -> return ()
  (BStmt (Block ss))  -> do modify (\s -> s {vars = ([]:vars s)})
                            mapM_ stmtCode ss
                            modify (\s -> s {vars = tail (vars s)})
  Decl t is           -> case is of
                          [] -> return ()
                          (NoInit id:is') -> addVar t id >> stmtCode (Decl t is')
                          (Init id expr:is') ->
                             do exprCode expr
                                addVar t id
                                case t of Int -> do  i <- lookupId id
                                                     istore i
                                                     stmtCode (Decl t is')
                                          Doub -> do i <- lookupId id
                                                     dstore i
                                                     stmtCode (Decl t is')
  Ass id e@(TExp t _) -> lookupId id >>= (\i -> case t of
                                                  Int  -> exprCode e >> istore i
                                                  Doub -> exprCode e >> dstore i)
  Incr id             -> lookupId id >>= iinc
  Decr id             -> lookupId id >>= idec
  Ret e@(TExp t _)    -> do exprCode e
                            case t of
                              Int  -> iret
                              Doub -> dret
  VRet                -> ret
  Cond expr stmt      -> do l <-      getLabel
                            bipush    0
                            exprCode  expr
                            if_icmpeq l
                            stmtCode  stmt
                            putLabel  l
  CondElse expr s0 s1 -> do l1 <-     getLabel
                            l2 <-     getLabel
                            bipush    0
                            exprCode  expr
                            if_icmpeq l1
                            stmtCode  s0 -- true
                            goto      l2
                            putLabel  l1
                            stmtCode  s1 -- false
                            putLabel  l2
  While expr stmt     -> do l1 <- getLabel
                            l2 <- getLabel
                            putLabel l1
                            bipush 0      -- push False
                            exprCode expr -- this shuld be exither true or false
                            if_icmpeq l2
                            stmtCode stmt
                            goto l1 -- loop
                            putLabel l2 -- end loop
  SExp e@(TExp t e')  ->    exprCode e >> case t of -- not sure if this is correct
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
  EVar id      -> lookupId id >>=  case t of Int -> iload;  Doub -> dload
  ELitInt i    -> bipush i
  ELitDoub d   -> dpush d
  ELitTrue     -> bipush 1
  ELitFalse    -> bipush 0
  EApp (Ident "printString") [TExp _ (EString s)] ->printStream >> spush s  >> 
                                                    incStack (-1) >> println 'S'
  EApp (Ident "printInt") es    -> printStream >> mapM_ exprCode es >> 
                                   mapM_ popExpr es >> println 'I'
  EApp (Ident "printDouble") es -> printStream >> mapM_ exprCode es >> 
                                   mapM_ popExpr es >> println 'D'
  EApp (Ident "readInt") es     -> undefined
  EApp (Ident "readDouble") es  -> undefined
  EApp (Ident id) es -> mapM_ exprCode es >> mapM_ popExpr es >> invokestatic t id es
  EString s    -> spush s
  Neg exp      -> undefined
  Not exp      -> undefined
  EMul e0 o e1 -> exprCode e0 >> exprCode e1 >>
                  case t of Int  -> case o of 
                                      Div   -> idiv
                                      Mod   -> imod
                                      Times -> imul
                            Doub -> case o of 
                                      Div   -> ddiv
                                      Mod   -> dmod
                                      Times -> dmul
  EAdd e0 o e1 -> exprCode e0 >> exprCode e1 >>
                  case t of Int  -> case o of
                                      Plus  -> iadd
                                      Minus -> isub
                            Doub -> case o of
                                      Plus  -> dadd
                                      Minus -> dsub
  ERel e0 o e1 -> do l1 <- getLabel
                     l2 <- getLabel
                     exprCode e0
                     exprCode e1
                     case o of
                       LTH -> if_icmplt l1
                       LE  -> if_icmple l1
                       GTH -> if_icmpgt l1
                       GE  -> if_icmpge l1
                       EQU -> if_icmpeq l1
                       NE  -> if_icmpne l1
                     bipush   0
                     goto     l2
                     putLabel l1
                     bipush   1
                     putLabel l2
  EAnd e0 e1   -> exprCode e0 >> exprCode e1 >> iand
  EOr  e0 e1   -> exprCode e0 >> exprCode e1 >> ior
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Jasmin Instructions
--------------------------------------------------------------------------------
iload  n    = putCode ["\tiload "  ++ (show n)] >> incStack 1
istore n    = putCode ["\tistore " ++ (show n)] >> incStack (-1)
dload  n    = putCode ["\tdload "  ++ (show n)] >> incStack 2
dstore n    = putCode ["\tdstore " ++ (show n)] >> incStack (-2)
bipush n    = putCode ["\tbipush " ++ (show n)] >> incStack 1
dpush  n    = putCode ["\tldc2_w " ++ (show n)] >> incStack 2
spush  s    = putCode ["\tldc "    ++ (show s)] >> incStack 1
imul        = putCode ["\timul"] >> incStack (-1)
idiv        = putCode ["\tidiv"] >> incStack (-1)
imod        = putCode ["\timod"] >> incStack (-1)
dmul        = putCode ["\tdmul"] >> incStack (-2)
dmod        = putCode ["\tdmod"] >> incStack (-2)
ddiv        = putCode ["\tddiv"] >> incStack (-2)
iadd        = putCode ["\tiadd"] >> incStack (-1)
isub        = putCode ["\tisub"] >> incStack (-1)
dadd        = putCode ["\tdadd"] >> incStack (-2)
dsub        = putCode ["\tdsub"] >> incStack (-2)
ipop        = putCode ["\tpop"]  >> incStack (-1)
dpop        = putCode ["\tpop2"] >> incStack (-2)
iret        = putCode ["\tireturn"]
dret        = putCode ["\tdreturn"]
ret         = putCode ["\treturn"]
iinc n      = putCode ["\tiinc " ++ show n ++ " 1"]
idec n      = putCode ["\tiinc " ++ show n ++ " -1"]
iand        = putCode ["\tand"] >> incStack (-1)
ior         = putCode ["\tor"]  >> incStack (-1)
goto      l = putCode ["\tgoto " ++ l]
if_icmplt l = putCode ["\tif_icmplt " ++ l] >> incStack (-2)
if_icmple l = putCode ["\tif_icmple " ++ l] >> incStack (-2)
if_icmpgt l = putCode ["\tif_icmpgt " ++ l] >> incStack (-2)
if_icmpge l = putCode ["\tif_icmpge " ++ l] >> incStack (-2)
if_icmpeq l = putCode ["\tif_icmpeq " ++ l] >> incStack (-2)
if_icmpne l = putCode ["\tif_icmpne " ++ l] >> incStack (-2)
printStream = putCode ["\tgetstatic java/lang/System/out Ljava/io/PrintStream;"] >>
              incStack 1
println c   = putCode ["\tinvokevirtual java/io/PrintStream/println("++s++")V"]  >> 
              incStack (-1)
                   where s = case c of 'S' -> "Ljava/lang/String;"
                                       'I' -> "I"
                                       'D' -> "D"
invokestatic t id es = 
    do s <- get
       putCode ["\tinvokestatic " ++ className s ++ "/" ++ id ++
                "(" ++ map exprToChar es ++ ")" ++ [typeToChar t]]
       case t of Void -> return ()
                 Int  -> incStack 1
                 Doub -> incStack 2
putLabel l  = putCode [l++":"]
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Util functions
--------------------------------------------------------------------------------
-- | converts a Type to it's Char representation.
typeToChar :: Type -> Char
typeToChar t = fromJust $ lookup t [(Int,'I'),(Doub,'D'),(Void,'V')]

-- | Convert an expression to the Char representation of it's type.
exprToChar :: Expr -> Char
exprToChar (TExp t _) = typeToChar t

-- | Reduces the stack-counter by the stack-space of the type of the expression.
popExpr :: Expr -> Result ()
popExpr (TExp _ (EString _)) = incStack (-1)
popExpr (TExp t _) = case t of Int  -> incStack (-1)
                               Doub -> incStack (-2)
                               Void -> return ()
--------------------------------------------------------------------------------
