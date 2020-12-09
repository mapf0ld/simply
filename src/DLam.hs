module DLam where

--import           Control.Monad (unless)

data Name
    = Const String
    | Bound Int
    | Unquoted Int
    deriving Show
