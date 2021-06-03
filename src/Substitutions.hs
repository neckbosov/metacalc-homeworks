{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Substitutions where

import AST
import Env
import Restrictions

data SBind = CVar :-> CExp
  deriving (Show)

type Subst = [SBind]

dom :: Subst -> [CExp]
dom subst = [cvar | (cvar :-> _) <- subst]

instance APPLY CExp Subst where
  (ATOM a) /. s = ATOM a
  (CONS h t) /. s = CONS (h /. s) (t /. s)
  cvar /. s
    | cvar `notElem` dom s = cvar
    | otherwise = head [cexp | (cv :-> cexp) <- s, cv == cvar]

instance APPLY InEq Subst where
  (l :=/=: r) /. subst = (l /. subst) :=/=: (r /. subst)

instance APPLY CBind Subst where
  (pvar := cexpr) /. subst = pvar := (cexpr /. subst)

--instance APPLY a subst => APPLY [a] subst where
--  cxs /. subst = map (/. subst) cxs

instance (APPLY a Subst, APPLY b Subst) => APPLY (a, b) Subst where
  (ax, bx) /. subst = (ax /. subst, bx /. subst)

instance APPLY Restr Subst where
  INCONSISTENT /. subst = INCONSISTENT
  (RESTR ineqs) /. subst = cleanRestr $ RESTR $ ineqs /. subst

instance APPLY Term Subst where
  (ALT cond t1 t2) /. subst = ALT (cond /. subst) (t1 /. subst) (t2 /. subst)
  (CALL name exps) /. subst = CALL name (exps /. subst)
  (RETURN exp) /. subst = RETURN (exp /. subst)

instance APPLY Cond Subst where
  (EQA' x y) /. subst = EQA' (x /. subst) (y /. subst)
  (CONS' exp h t a) /. subst = CONS' (exp /. subst) h t a