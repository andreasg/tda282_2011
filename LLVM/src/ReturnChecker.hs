module ReturnChecker where

import AbsJavalette

--------------------------------------------------------------------------------
-- Return checker
--------------------------------------------------------------------------------
-- |Check if all branches of a topdef actually returns
returnCheck :: [TopDef] -> Bool
returnCheck fs = not $ elem False (map (\(FnDef _ _ _ (Block stms)) -> returns stms) fs')
    where fs' = filter (\(FnDef t _ _ _) -> t /= Void) fs -- get the non-void funs


-- |Check if a statement ultimatly returns
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
--------------------------------------------------------------------------------