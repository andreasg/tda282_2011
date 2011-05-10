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
data Value = VReg Type Register | VPtr Type Register | VInt Integer 
           | VDoub Double       | VBit Integer       | VString Int String
           | VArr Type [Integer] Register

instance Show Value where
    show (VReg t r) = llvmType t ++ " " ++  show r
    show (VPtr t r) = llvmType t ++ "* " ++ show r
    show (VInt i)   = llvmType Int ++ " " ++ show i
    show (VDoub d)  = llvmType Doub ++ " " ++ show d
    show (VBit i)   = "i1 " ++ show i
    show (VArr t ls r) = f ls t ++ " " ++ show r
        where f (i:[]) t = "[ " ++ show i ++ " x " ++ llvmType t ++ " ]"
              f (i:is) t = "[ " ++ show i ++ " x " ++ f is t ++ " ]"
    show (VString len s) = "i8* getelementptr inbounds ([" ++ show (len+1) ++ " x i8]* @."++s++", i32 0, i32 0)"

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
  , vars         :: [[(Ident,(Type,Register))]] -- variables
  , funs         :: [(Ident,Type)]     -- function types
  , code         :: [String]
  }
emptyEnv :: Env
emptyEnv = Env 1 -- register count
               0  -- labels
               []  -- strings
               [ [],[] ] -- vars
               [] -- functions
               [] -- code
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
         "declare i8*  @calloc(i32, i32)\n" ++
         "declare double @readDouble()\n\n" 
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Run Functions
--------------------------------------------------------------------------------
-- | Generates LLVM code for a Javalette program.
genCode :: Program -> String
genCode p = let (_,e) = runEnv p
            in  unlines (header : strings e  ++  (reverse $ code e))

-- | Evaluates an environment
runEnv :: Program -> ((),Env)
runEnv (Program topDefs) = runState (mapM_ topdefCode topDefs) emptyEnv
--------------------------------------------------------------------------------


-- | Get the string repr. of a Value without it's type.
unValue :: Value -> String
unValue (VPtr _ r) = show r
unValue (VReg _ r) = show r
unValue (VInt i)   = show i
unValue (VDoub d)  = show d
unValue (VBit i )  = show i

-- | Determine if a LLVM value is of Integer type
isInt :: Value     -> Bool
isInt (VReg Int _)  = True
isInt (VReg Bool _) = True
isInt (VReg _ _)    = False
isInt (VPtr _ _)    = False
isInt (VInt _)      = True
isInt (VDoub _)     = False
isInt (VBit i)      = True

isInts :: Value -> Value -> Bool
isInts a b = isInt a && isInt b
--------------------------------------------------------------------------------