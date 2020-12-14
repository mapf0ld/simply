module DLam where

import           Control.Monad (unless)

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
    | App InferTerm CheckTerm
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
evalInferT (App e1 e2) env = vapp (evalInferT e1 env) (evalCheckT e2 env)
evalInferT Star _          = VStar
evalInferT (Pi t1 t2) env  = VPi (evalCheckT t1 env)
                                 (\x -> evalCheckT t2 (x : env))

evalCheckT :: CheckTerm -> Env -> Value
evalCheckT (Infer e) env = evalInferT e env
evalCheckT (Lam t) env   = VLam (\x -> evalCheckT t (x : env))

iSubst :: Int -> InferTerm -> InferTerm -> InferTerm
iSubst i r (Ann e t)   = Ann (cSubst i r e) t
iSubst i r (Var j)     = if i == j then r else Var j
iSubst _ _ (Par y)     = Par y
iSubst i r (App e1 e2) = App (iSubst i r e1) (cSubst i r e2)
iSubst _ _ Star        = Star
iSubst i r (Pi t t')   = Pi (cSubst i r t) (cSubst (i + 1) r t')

cSubst :: Int -> InferTerm -> CheckTerm -> CheckTerm
cSubst i r (Infer e) = Infer (iSubst i r e)
cSubst i r (Lam e)   = Lam (cSubst (i + 1) r e)

varpar :: Int -> Name -> InferTerm
varpar i (Unquoted k) = Var (i - k - 1)
varpar _ x            = Par x

neutralQuote :: Int -> Neutral -> InferTerm
neutralQuote i (NPar x)   = varpar i x
neutralQuote i (NApp n v) = App (neutralQuote i n) (quote i v)

quoteZ :: Value -> CheckTerm
quoteZ = quote 0

quote :: Int -> Value -> CheckTerm
quote i (VLam f)     = Lam (quote (i + 1) (f (vpar (Unquoted i))))
quote i (VNeutral n) = Infer (neutralQuote i n)
quote _ VStar        = Infer Star
quote i (VPi v f)    = Infer (Pi (quote i v)
                                 (quote (i + 1) (f (vpar (Unquoted i)))))

type Result a = Either String a

typeOfInferT :: Int -> Context -> InferTerm -> Result Type
typeOfInferT i ctxt (Ann e t)
  = do typeOfCheckT i ctxt t VStar
       let v = evalCheckT t []
       typeOfCheckT i ctxt e v
       return v

typeOfInferT _ _ Star
  = return VStar

typeOfInferT i ctxt (Pi t t')
  = do typeOfCheckT i ctxt t VStar
       let v = evalCheckT t []
       typeOfCheckT (i + 1) ((Bound i, v) : ctxt)
                    (cSubst 0 (Par (Bound i)) t') VStar
       return VStar

typeOfInferT _ ctxt (Par x)
  = case lookup x ctxt of
      Just v  -> return v
      Nothing -> Left "unknown identifier"

typeOfInferT i ctxt (App e1 e2)
  = do sigma <- typeOfInferT i ctxt e1
       case sigma of
         VPi v f -> do typeOfCheckT i ctxt e2 v
                       return (f (evalCheckT e2 []))
         _       -> Left "illegal application"
typeOfInferT _ _ _
  = Left "Unreachable"

typeOfCheckT :: Int -> Context -> CheckTerm -> Type -> Result ()
typeOfCheckT i ctxt (Infer e) t
  = do e' <- typeOfInferT i ctxt e
       unless (quoteZ t == quoteZ e') (Left "type mismatch")
typeOfCheckT i ctxt (Lam e) (VPi v f)
  = typeOfCheckT (i + 1) ((Bound i, v) : ctxt)
                (cSubst 0 (Par (Bound i)) e) (f (vpar (Bound i)))
typeOfCheckT _ _ _ _ = Left "type mismatch"
