module SLam where

-- name for free variables
data Name
    = Const String
    | Bound Int
    | Unquoted Int
    deriving (Show, Eq)


data InferTerm =
    Ann CheckTerm Type
    | Var Int
    | Par Name
    | App InferTerm CheckTerm

data CheckTerm
    = Infer InferTerm
    | Lam CheckTerm

-- a value is either a neutral term, i.e.
-- a variable applied to (possibly empty) sequence of vars,
-- or it is a lambda abstraction
data Neutral
    = NPar Name
    | NApp Neutral Value

data Value
    = VLam (Value -> Value)
    | VNeutral Neutral


data Type
    = TPar Name
    | Fun Type Type
    deriving (Show, Eq)

type Env = [Value]

vpar :: Name -> Value
vpar = VNeutral . NPar

evalInfer :: InferTerm -> Env -> Value
evalInfer (Ann e _) env   = evalCheck e env
evalInfer (Par x) _       = vpar x
evalInfer (Var i) env     = env !! i
evalInfer (App e1 e2) env = vapp (evalInfer e1 env) (evalCheck e2 env)

vapp :: Value -> Value -> Value
vapp (VLam f) x     = f x
vapp (VNeutral n) v = VNeutral (NApp n v)

evalCheck :: CheckTerm -> Env -> Value
evalCheck (Infer e)  env = evalInfer e env
evalCheck (Lam e) env    = VLam (\x -> evalCheck e (x : env))


iSubst :: Int -> InferTerm -> InferTerm -> InferTerm
iSubst i r (Ann e tau) = Ann (cSubst i r e) tau
iSubst i r (Var j)     = if i == j then r else Var j
iSubst _ _ (Par y)     = Par y
iSubst i r (App e1 e2) = App (iSubst i r e1) (cSubst i r e2)

cSubst :: Int -> InferTerm -> CheckTerm -> CheckTerm
cSubst i r (Infer e) = Infer (iSubst i r e)
cSubst i r (Lam e)   = Lam (cSubst (i + 1) r e)

data Kind = Star deriving Show

data Info =
    HasKind Kind
    | HasType Type
    deriving Show

type Context = [(Name, Info)]

kindOfInfer :: Context -> Type -> Kind -> Maybe ()
kindOfInfer ctxt (TPar i) Star
  = case lookup i ctxt of
      Just (HasKind Star) -> return ()
      Nothing             -> error "Unknown identifier"
kindOfInfer ctxt (Fun t1 t2) Star
  = do kindOfInfer ctxt t1 Star
       kindOfInfer ctxt t2 Star

-- partial, infinite loop
typeCheckZ :: Context -> InferTerm -> Maybe Type
typeCheckZ = typeCheckZ


