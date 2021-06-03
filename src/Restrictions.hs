{-# LANGUAGE TypeSynonymInstances #-}

module Restrictions where

import AST
import Data.List (nub)
import Env

type CVar = Exp

type CExp = Exp

type CBind = Bind

type CEnv = Env

type CExps = [CExp]

type CVars = [CVar]

data InEq = CExp :=/=: CExp
  deriving (Show)

data Restr = INCONSISTENT | RESTR [InEq]
  deriving (Eq, Show)

instance Eq InEq where
  (l1 :=/=: r1) == (l2 :=/=: r2)
    | l1 == l2 && r1 == r2 = True
    | l1 == r2 && r1 == l2 = True
    | otherwise = False

isContradiction, isTautology :: InEq -> Bool
isContradiction (left :=/=: right) = left == right
isTautology (ATOM a :=/=: ATOM b) = a /= b
isTautology (left :=/=: right) = False

cleanRestr :: Restr -> Restr
cleanRestr INCONSISTENT = INCONSISTENT
cleanRestr (RESTR ineqs)
  | any isContradiction ineqs = INCONSISTENT
  | otherwise = RESTR $ nub $ filter (not . isTautology) ineqs

instance UPDATE Restr where
  INCONSISTENT +. _ = INCONSISTENT
  _ +. INCONSISTENT = INCONSISTENT
  (RESTR r1) +. (RESTR r2) = cleanRestr $ RESTR (r1 ++ r2)

class CVARS a where cvars :: a -> [CExp]

instance CVARS CExp where
  cvars (ATOM _) = []
  cvars cvar@(CVA _) = [cvar]
  cvars cvar@(CVE _) = [cvar]
  cvars (CONS h t) = nub $ cvars h ++ cvars t

instance CVARS InEq where
  cvars (ax :=/=: bx) = nub $ cvars ax ++ cvars bx

instance CVARS CBind where
  cvars (pvar := cx) = cvars cx

instance CVARS c => CVARS [c] where
  cvars cxs = nub $ concat $ map cvars cxs

instance CVARS Restr where
  cvars INCONSISTENT = []
  cvars (RESTR ineqs) = cvars ineqs

instance (CVARS a, CVARS b) => CVARS (a, b) where
  cvars (ax, bx) = nub $ cvars ax ++ cvars bx
