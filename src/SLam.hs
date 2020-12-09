module SLam where

import           Control.Monad (unless)

-- name for free variables
data Name
    = Const String
    | Bound Int -- Bound variable, de-bruijn indices,
    | Unquoted Int -- unquoted var, de-bruijn indices
    deriving (Show, Eq)

data InferTerm =
    Ann CheckTerm Type -- annotated term
    | Var Int -- variable, de-bruijn indices
    | Par Name -- free variable name
    | App InferTerm CheckTerm -- term application
    deriving (Show, Eq)

data CheckTerm
    = Infer InferTerm -- type-checkable term is inferrable
    | Lam CheckTerm -- lambda abstraction
    deriving (Show, Eq)

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
    = TPar Name -- name of a type variable
    | Fun Type Type -- Function type (* -> *)
    deriving (Show, Eq)

type Env = [Value] -- environment

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


-- substitution rules implemented for inferrable terms
iSubst :: Int -> InferTerm -> InferTerm -> InferTerm
iSubst i r (Ann e tau) = Ann (cSubst i r e) tau
iSubst i r (Var j)     = if i == j then r else Var j -- found the variable for substitution
iSubst _ _ (Par y)     = Par y -- let the free vars be intact
iSubst i r (App e1 e2) = App (iSubst i r e1) (cSubst i r e2) -- structual recursion

-- subst for checkable terms
cSubst :: Int -> InferTerm -> CheckTerm -> CheckTerm
cSubst i r (Infer e) = Infer (iSubst i r e)
cSubst i r (Lam e)   = Lam (cSubst (i + 1) r e)


data Kind = Star deriving Show
data Info = HasKind Kind | HasType Type deriving Show
type Context = [(Name, Info)]
type Result a = Either String a

-- kind of inferrable terms
kindInferT :: Context -> Type -> Kind -> Result ()
kindInferT ctxt (TPar i) Star
  = case lookup i ctxt of
      Just (HasKind Star) -> return ()
      Nothing             -> error "Unknown identifier"
kindInferT ctxt (Fun t1 t2) Star
  = do kindInferT ctxt t1 Star
       kindInferT ctxt t2 Star


-- type checker for inferrable terms, with de-bruijn index starting from 0
typeOfInferZ :: Context -> InferTerm -> Result Type
typeOfInferZ = typeOfInferT 0

typeOfInferT :: Int -> Context -> InferTerm -> Result Type
typeOfInferT i ctxt (Ann e t)
  = do kindInferT ctxt t Star
       typeOfCheckT i ctxt e t
       return t
typeOfInferT _ ctxt (Par x)
  = case lookup x ctxt of
      Just (HasType t) -> return t
      _                -> error "unknown identifier"
typeOfInferT i ctxt (App e1 e2)
  = do sigma <- typeOfInferT i ctxt e1
       case sigma of
         Fun t t' -> do typeOfCheckT i ctxt e2 t
                        return t'
         _ -> error "illegal application"
typeOfInferT _ _ _ = Left "Unreachable"

typeOfCheckT :: Int -> Context -> CheckTerm -> Type -> Result ()
typeOfCheckT i ctxt (Infer e) t
  = do t' <- typeOfInferT i ctxt e
       unless (t == t') (error "type mismatch")

typeOfCheckT i ctxt (Lam e) (Fun t t')
  = typeOfCheckT (i + 1)
                 ((Bound i, HasType t) : ctxt)
                 (cSubst 0 (Par (Bound i)) e) t'

-- below are quotation of values for displaying and debugging
--
quoteZ :: Value -> CheckTerm
quoteZ = quote 0

quote :: Int -> Value -> CheckTerm
quote i (VLam f)     = Lam (quote (i + 1) (f (vpar (Unquoted i))))
quote i (VNeutral n) = Infer (neutralQuote i n)

neutralQuote :: Int -> Neutral -> InferTerm
neutralQuote i (NPar x)   = varpar i x
neutralQuote i (NApp n v) = App (neutralQuote i n) (quote i v)

varpar :: Int -> Name -> InferTerm
varpar i (Unquoted k) = Var (i - k - 1)
varpar _ x            = Par x

-- All the terms needed to be explicitly annotated with Ann
-- for the typechecker to work correctly.
id' = Lam (Infer (Var 0))
const' = Lam (Lam (Infer (Var 1)))
tpar a = TPar (Const a)
par x = Infer (Par (Const x))
termOne = App (Ann id' (Fun (tpar "a") (tpar "a"))) (par "y")
envOne = [(Const "y", HasType (tpar "a")), -- y = a
          (Const "a", HasKind Star)] -- a :: *

-- evaluation of `const y z --> y`, with y :: a, z :: b, const' :: a -> b -> a
termTwo = App (App (Ann const' (Fun (tpar "a") (Fun (tpar "b") (tpar "a")))) (par "y")) (par "z")
envTwo = [(Const "y", HasType (tpar "a")),
          (Const "z", HasType (tpar "b")),
          (Const "a", HasKind Star),
          (Const "b", HasKind Star)]

