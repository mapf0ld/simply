module SLam where

data InferTerm =
    Ann CheckTerm Type
    | Var Int
    | Par Int
    | App InferTerm CheckTerm

data CheckTerm
    = Infer InferTerm
    | Lam CheckTerm

data Value
    = VApp Int [Value]
    | VLam (Value -> Value)

data Type
    = TPar Int
    | Fun Type Type

iSubst :: Int -> InferTerm -> InferTerm -> InferTerm
iSubst i r (Ann e tau) = Ann (cSubst i r e) tau
iSubst i r (Var j)     = if i == j then r else Var j
iSubst _ _ (Par y)     = Par y
iSubst i r (App e1 e2) = App (iSubst i r e1) (cSubst i r e2)


cSubst :: Int -> InferTerm -> CheckTerm -> CheckTerm
cSubst i r (Infer e) = Infer (iSubst i r e)
cSubst i r (Lam e)   = Lam (cSubst (i + 1) r e)
