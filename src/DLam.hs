module DLam where

--import           Control.Monad (unless)

data Name
    = Const String
    | Bound Int
    | Unquoted Int
    deriving (Show, Eq)

data CheckTerm =
    Infer InferTerm
    | Lam CheckTerm -- Lambda abstraction
    deriving (Show, Eq)

data InferTerm =
    Ann CheckTerm CheckTerm
    | Star
    | Pi CheckTerm CheckTerm
    | Var Int
    | Par Name
    | App InferTerm InferTerm
      deriving (Show, Eq)

data Neutral =
    NPar Name
    | NApp Neutral Value

data Value =
    VLam (Value -> Value)
    | VStar
    | VPi Value (Value -> Value)
    | VNeutral Neutral

type Type = Value
type Context = [(Name, Type)]
type Env = [Value]

vpar :: Name -> Value
vpar = VNeutral . NPar

vapp :: Value -> Value -> Value
-- value application
vapp (VLam f) x     = f x
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp v1 v2          = error "no application applies" v1 v2

evalInferT :: InferTerm -> Env -> Value
evalInferT (Ann e _) env   = evalCheckT e env
evalInferT (Par x) _       = vpar x
evalInferT (Var i) env     = env !! i
evalInferT (App e1 e2) env = vapp (evalInferT e1 env) (evalInferT e2 env)
evalInferT Star _          = VStar
evalInferT (Pi t1 t2) env = VPi (evalCheckT t1 env)
                                (\x -> evalCheckT t2 (x : env))

evalCheckT :: CheckTerm -> Env -> Value
evalCheckT (Infer e) env = evalInferT e env
evalCheckT (Lam t) env   = VLam (\x -> evalCheckT t (x : env))

iSubst :: Int -> InferTerm -> InferTerm -> InferTerm
iSubst i r (Ann e t) = Ann (cSubst i r e) t

cSubst :: Int -> InferTerm -> CheckTerm -> CheckTerm
cSubst i r (Infer e) = Infer (iSubst i r e)
