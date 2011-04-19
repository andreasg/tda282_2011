module CodeGeneration (genCode) where

import AbsJavalette
import PrintJavalette
import ErrM
import Debug.Trace
import Data.List (nubBy, init, last)
import Data.Maybe (fromJust)
import Control.Monad.State

import ReturnChecker

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
                   , className     :: String           -- name of the java class
                   }
           deriving (Show,Eq)


-- |Create a new scope, the name should be the Id of the java class
newScope ::  String -> Scope
newScope name = Scope 0 0 [[]] 0 0 [] name
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
  s { code = [".method public static " ++ id ++
                "(" ++ concat (map typeToChar (map (\(Arg t id) -> t) args)) ++ ")" ++
                typeToChar t
             , ".limit stack "  ++ show (maxStackDepth s)
             , ".limit locals " ++ show (nextVar s)
             ] ++ code s }



-- | Generate a Jasmin class-header
classHeader :: String -> [String]
classHeader n = [".class public " ++ n,".super java/lang/Object\n"]


-- | Jasmin main function, this will call the Javalette
-- | main-function and then return.
main :: String ->[String]
main n = [".method public static main([Ljava/lang/String;)V"
         ,".limit stack 1"
         ,".limit locals 1"
         ,"\tinvokestatic " ++ n ++ "/main()I"
         ,"\tpop"
         ,"\treturn"
         ,".end method\n\n"
         ]


-- | Generate code for a TopDef, returns the computed scope and the TopDef
runTopDef :: String -> TopDef -> (Scope,TopDef)
runTopDef name t = (fst $ runState (topDefCode t) (newScope name), t)


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
  Bool  -> modify (\s -> s { vars = ((id,nextVar s):head (vars s)):tail (vars s)
                           , nextVar = nextVar s + 1})
  ArrInt  ds -> addVar Int id
  ArrDoub ds -> addVar Int id


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
                          (NoInit id:is') -> do addVar t id
                                                i <- lookupId id
                                                case t of
                                                 Int  -> bipush 0 >> istore i
                                                 Doub -> dpush 0.0 >> dstore i
                                                 Bool -> bipush 0 >> istore i
                                                 ArrInt  _ -> anull >> astore i
                                                 ArrDoub _ -> anull >> astore i
                                                stmtCode (Decl t is')
                          (Init id expr:is') ->
                             do exprCode expr
                                addVar t id
                                case t of Int  -> do i <- lookupId id
                                                     istore i
                                                     stmtCode (Decl t is')
                                          Doub -> do i <- lookupId id
                                                     dstore i
                                                     stmtCode (Decl t is')
                                          ArrInt _  -> do i <- lookupId id
                                                          astore i
                                                          stmtCode (Decl t is')
                                          ArrDoub _ -> do i <- lookupId id
                                                          astore i
                                                          stmtCode (Decl t is')
  Ass id e@(TExp t e') -> lookupId id >>= (\i -> case t of
                                                  Int  -> exprCode e >> istore i
                                                  Doub -> exprCode e >> dstore i
                                                  Bool -> exprCode e >> istore i
                                                  ArrInt  _ -> exprCode e >> astore i
                                                  ArrDoub _ -> exprCode e >> astore i)
  Incr id             -> lookupId id >>= iinc
  Decr id             -> lookupId id >>= idec
  Ret e@(TExp t _)    -> do exprCode e
                            case t of
                              Int  -> iret
                              Doub -> dret
                              Bool -> iret
                              ArrDoub _ -> aret
                              ArrInt  _ -> aret
  VRet                -> ret
  Cond (TExp Bool ELitTrue) stmt -> stmtCode stmt
  Cond (TExp Bool ELitFalse) stmt -> return ()
  Cond expr stmt      -> do l <-      getLabel
                            bipush    0
                            exprCode  expr
                            if_icmpeq l
                            stmtCode  stmt
                            putLabel  l
  CondElse (TExp Bool ELitTrue) s _ -> stmtCode s
  CondElse (TExp Bool ELitFalse) _ s-> stmtCode s
  CondElse expr s0 s1 ->  if returns [s0] && returns [s1]
                            then do l1 <-     getLabel
                                    exprCode  expr
                                    ifeq      l1
                                    stmtCode  s0
                                    putLabel  l1
                                    stmtCode  s1
                            else do l1 <-     getLabel
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

  ArrAss id ds0 e@(TExp t _) -> do lookupId id >>= aload
                                   mapM_ (\(EDimen e) -> exprCode e >> aaload) (init ds0)
                                   (\(EDimen e) -> exprCode e) (last ds0)
                                   exprCode e
                                   case t of
                                     Int -> iastore
                                     Doub -> dastore
                                     ArrInt _ -> aastore
                                     ArrDoub _ -> aastore

  For t' i0 i1 s -> do modify (\s -> s {vars = ([]:vars s)})
                       l1 <- getLabel
                       l2 <- getLabel

                       -- our element variable
                       addVar t' i0
                       elem <- lookupId i0

                       -- get the array
                       ar <- lookupId i1

                       -- create a count variable and init to 0
                       addVar Int (Ident "___counter___")
                       count <- lookupId (Ident "___counter___")
                       bipush 0
                       istore count

                       putLabel l1

                       iload count
                       aload ar
                       arraylength

                       if_icmpge   l2 -- jump to l2 if we are done

                       -- load the current value
                       aload ar
                       iload count
                       case t' of
                         Int  -> iaload >> istore elem
                         Doub -> daload >> dstore elem
                         ArrInt _ -> aaload >> astore elem
                         ArrDoub _ -> aaload >> astore elem

                       -- run the statemnt
                       stmtCode s

                       -- save the value
                       aload ar
                       iload count
                       case t' of
                         Int  -> iload elem >> iastore
                         Doub -> dload elem >> dastore
                         ArrInt _ -> aload elem >> aastore
                         ArrDoub _ -> aload elem >> aastore

                       -- increment
                       iinc count

                       -- jump
                       goto l1

                       -- done
                       putLabel l2

                       -- exit the scope
                       modify (\s -> s {vars = tail (vars s)})
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Expression Code Generation
--------------------------------------------------------------------------------
-- |Generate code for an expression
exprCode :: Expr -> Result ()
exprCode (TExp t e) =
 case e of
  EVar id      -> lookupId id >>=  case t of Int     -> iload;  Doub   -> dload;
                                             Bool    -> iload;  ArrInt _ -> aload;
                                             ArrDoub _ -> aload;
  ELitInt i    -> bipush i
  ELitDoub d   -> dpush d
  ELitTrue     -> bipush 1
  ELitFalse    -> bipush 0
  EApp (Ident "printString") [TExp _ (EString s)] -> spush s  >>
                                                    incStack (-1) >> sprint
  EApp (Ident "printInt") es    -> mapM_ exprCode es >> mapM_ popExpr es >> iprint
  EApp (Ident "printDouble") es -> mapM_ exprCode es >> mapM_ popExpr es >> dprint
  EApp (Ident "readInt")    _   -> iread
  EApp (Ident "readDouble") _   -> dread
  EApp (Ident id) es -> mapM_ exprCode es >> mapM_ popExpr es >> invokestatic t id es
  EString s    -> spush s
  Neg exp      -> case t of
                    Int  -> exprCode exp >> ineg
                    Doub -> exprCode exp >> dneg
                    Bool -> exprCode exp >> bipush 1 >> ixor
  Not exp      -> case t of
                    Int  -> do l1 <- getLabel
                               l2 <- getLabel
                               exprCode exp
                               ifeq     l1
                               bipush   1
                               goto     l2
                               putLabel l1
                               bipush   0
                               putLabel l2
                    Doub -> do l1 <- getLabel
                               l2 <- getLabel
                               dload 0.0
                               exprCode exp
                               dcmpg
                               ifeq     l1
                               bipush   1
                               goto     l2
                               putLabel l1
                               bipush   0
                               putLabel l2
                    Bool -> exprCode exp >> bipush 1 >> ixor
  EMul e0 o e1 -> exprCode e0 >> exprCode e1 >>
                  case t of Int  -> case o of
                                      Div   -> idiv
                                      Mod   -> imod
                                      Times -> imul
                            Doub -> case o of
                                      Div   -> ddiv
                                      Mod   -> dmod
                                      Times -> dmul
  EAdd e0 o e1 -> do exprCode e0
                     exprCode e1
                     case t of
                       Int  -> case o of
                                 Plus  -> iadd
                                 Minus -> isub
                       Doub -> case o of
                                 Plus  -> dadd
                                 Minus -> dsub
  ERel e0@(TExp t' _) o e1 -> do l1 <- getLabel
                                 l2 <- getLabel
                                 exprCode e0
                                 exprCode e1
                                 if t' == Doub
                                  then dcmpg >>
                                       case o of
                                         LTH -> iflt l1
                                         LE  -> ifle l1
                                         GTH -> ifgt l1
                                         GE  -> ifge l1
                                         EQU -> ifeq l1
                                         NE  -> ifne l1
                                  else case o of
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
  EAnd e0 e1   -> do l1 <-     getLabel
                     l2 <-     getLabel
                     l3 <-     getLabel
                     bipush    0
                     exprCode  e0
                     if_icmpeq l1 -- e0 == false
                     bipush    0
                     exprCode  e1
                     if_icmpeq l1  -- e1 == false
                     goto      l2  -- e0 && e1 == true
                     putLabel  l1  -- false
                     bipush    0
                     goto      l3
                     putLabel  l2  -- true
                     bipush    1
                     putLabel  l3
  EOr  e0 e1   -> do l1 <-     getLabel
                     l2 <-     getLabel
                     bipush    1
                     exprCode  e0
                     if_icmpeq l1 -- e0 || e1 == true
                     bipush    1
                     exprCode  e1
                     if_icmpeq l1 -- e1 == true
                     bipush    0
                     goto      l2
                     putLabel  l1  -- true
                     bipush    1
                     putLabel  l2
  EArr    t  [EDimen e] -> case t of
                    Int  -> exprCode e >> newarray "int"
                    Doub -> exprCode e >> newarray "double"
  EArr    t'  ds -> do mapM_ (\(EDimen e) -> exprCode e) ds
                       multianewarray (typeArr t) (length ds)
     where typeArr (ArrInt ds)  = (take (length ds) (repeat '[')) ++ "I"
           typeArr (ArrDoub ds) = (take (length ds) (repeat '[')) ++ "D"
  EArrLen id   -> (lookupId id >>= aload) >> arraylength
  EArrMDLen id ds -> do i <- lookupId id
                        aload i
                        mapM_ (\(EDimen e) -> exprCode e >> aaload) ds
                        arraylength
  EArrIdx id [EDimen e] -> do lookupId id >>= aload
                              exprCode e
                              case t of
                                Doub -> daload
                                Int  -> iaload
                                (ArrInt _)  -> aaload
                                (ArrDoub _) -> aaload
  EArrIdx id ds -> do lookupId id >>= aload
                      mapM_ (\(EDimen e) -> exprCode e >> aaload) (init ds)
                      (\(EDimen e) -> exprCode e) (last ds)
                      case t of
                        Int  -> iaload
                        Doub -> daload
                        (ArrInt _)  -> aaload
                        (ArrDoub _) -> aaload

exprCode e = trace (show e) (return ())
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Jasmin Instructions
--------------------------------------------------------------------------------
anull       = putCode ["\taconst_null"] >> incStack 1
aret        = putCode ["\tareturn"] >> incStack (-1)
aaload      = putCode ["\taaload"] >> incStack (-1)
aastore     = putCode ["\taastore"] >> incStack (-3)
aload     n = putCode ["\taload " ++ (show n)] >> incStack 1
iastore     = putCode ["\tiastore"] >> incStack (-3)
dastore     = putCode ["\tdastore"] >> incStack (-4)
astore    n = putCode ["\tastore " ++ (show n)] >> incStack (-1)
daload      = putCode ["\tdaload"]
iaload      = putCode ["\tiaload"] >> incStack (-1)
newarray  a = putCode ["\tnewarray " ++ a]
multianewarray t n = putCode["\tmultianewarray " ++ t ++ " " ++ show n] >> case head (reverse t) of
                                                                             'D' -> incStack ((-n)*2+1)
                                                                             'I' -> incStack ((-n)+1)
arraylength = putCode ["\tarraylength"]
iload  n    = putCode ["\tiload "  ++ (show n)] >> incStack 1
istore n    = putCode ["\tistore " ++ (show n)] >> incStack (-1)
dload  n    = putCode ["\tdload "  ++ (show n)] >> incStack 2
dstore n    = putCode ["\tdstore " ++ (show n)] >> incStack (-2)
bipush n    = putCode ["\tldc " ++ (show n)] >> incStack 1
dpush  n    = putCode ["\tldc2_w " ++ (show n)] >> incStack 2
spush  s    = putCode ["\tldc "    ++ (show s)] >> incStack 1
imul        = putCode ["\timul"] >> incStack (-1)
idiv        = putCode ["\tidiv"] >> incStack (-1)
imod        = putCode ["\tirem"] >> incStack (-1)
dmul        = putCode ["\tdmul"] >> incStack (-2)
dmod        = putCode ["\tdrem"] >> incStack (-2)
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
ixor        = putCode ["\tixor"]
ineg        = putCode ["\tineg"]
dneg        = putCode ["\tdneg"]
goto      l = putCode ["\tgoto " ++ l]
dcmpg       = putCode ["\tdcmpg"] >> incStack (-3)
if_icmplt l = putCode ["\tif_icmplt " ++ l] >> incStack (-2)
if_icmple l = putCode ["\tif_icmple " ++ l] >> incStack (-2)
if_icmpgt l = putCode ["\tif_icmpgt " ++ l] >> incStack (-2)
if_icmpge l = putCode ["\tif_icmpge " ++ l] >> incStack (-2)
if_icmpeq l = putCode ["\tif_icmpeq " ++ l] >> incStack (-2)
if_icmpne l = putCode ["\tif_icmpne " ++ l] >> incStack (-2)
iflt l = putCode ["\tiflt " ++ l] >> incStack (-1)
ifle l = putCode ["\tifle " ++ l] >> incStack (-1)
ifgt l = putCode ["\tifgt " ++ l] >> incStack (-1)
ifge l = putCode ["\tifge " ++ l] >> incStack (-1)
ifeq l = putCode ["\tifeq " ++ l] >> incStack (-1)
ifne l = putCode ["\tifne " ++ l] >> incStack (-1)
iprint      = putCode ["\tinvokestatic Runtime/printInt(I)V"] -- >> incStack (-1)
iread       = putCode ["\tinvokestatic Runtime/readInt()I"]    >> incStack 1
dprint      = putCode ["\tinvokestatic Runtime/printDouble(D)V"] -- >> incStack (-2)
dread       = putCode ["\tinvokestatic Runtime/readDouble()D"] >> incStack 2
sprint      = putCode ["\tinvokestatic Runtime/printString(Ljava/lang/String;)V"]
invokestatic t id es =
    do s <- get
       putCode ["\tinvokestatic " ++ className s ++ "/" ++ id ++
                "(" ++ concat (map exprToChar es) ++ ")" ++ typeToChar t]
       case t of Void    -> return ()
                 Int     -> incStack 1
                 Bool    -> incStack 1
                 Doub    -> incStack 2
                 ArrInt _ -> incStack 1
                 ArrDoub _-> incStack 1
putLabel l  = putCode [l++":"]
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Util functions
--------------------------------------------------------------------------------
-- | converts a Type to it's Char representation.
typeToChar :: Type -> String
typeToChar t = case t of
                 Int  -> "I"
                 Doub -> "D"
                 Void -> "V"
                 Bool -> "I"
                 ArrInt ds  -> (take (length ds) (repeat '['))++"I"
                 ArrDoub ds -> (take (length ds) (repeat '['))++"D"



--fromJust $ lookup t [(Int,"I"),(Doub,"D"),(Void,"V"),(Bool,"I"),(ArrInt,"[I"),(ArrDoub,"[D")]

-- | Convert an expression to the Char representation of it's type.
exprToChar :: Expr -> String
exprToChar (TExp t _) = typeToChar t
-- | Reduces the stack-counter by the stack-space of the type of the expression.
popExpr :: Expr -> Result ()
popExpr (TExp _ (EString _)) = incStack (-1)
popExpr (TExp t _) = case t of Int  -> incStack (-1)
                               Doub -> incStack (-2)
                               Bool -> incStack (-1)
                               ArrInt _ -> incStack (-1)
                               ArrDoub _ -> incStack (-1)
                               Void -> return ()
--------------------------------------------------------------------------------
