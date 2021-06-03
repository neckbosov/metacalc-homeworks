{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Env where

import AST
import Data.List (nub)


type State = (Term, Env)

data Bind = Var := Exp
  deriving (Show)

type Env = [Bind]

class APPLY a b where (/.) :: a -> b -> a

instance APPLY Exp Env where
  (ATOM a) /. env = ATOM a
  (CONS h t) /. env = CONS (h /. env) (t /. env)
  var /. env = head [x | (v := x) <- env, v == var]

instance APPLY a b => APPLY [a] b where
  xs /. y = map (/. y) xs

instance Eq Bind where
  (var1 := _) == (var2 := _) = var1 == var2

class UPDATE a where (+.) :: a -> a -> a

instance UPDATE Env where
  binds +. binds' = nub (binds' ++ binds)

mkEnv :: [Var] -> [EVal] -> Env
mkEnv = zipWith (:=)