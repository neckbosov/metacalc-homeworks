{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Classes where

import AST
import Env
import Restrictions
import Substitutions
import Unify (Clash (..))

type Class = (CExps, Restr)

type Conf = ((Term, CEnv), Restr)

data Contr = S Subst | R Restr
  deriving (Show)

type Split = (Contr, Contr)

type Classes = [Class]

idC, emptC :: Contr
idC = S []
emptC = R INCONSISTENT

instance APPLY c Subst => APPLY (c, Restr) Contr where
  (cx, rs) /. (S subst) = (cx /. subst, rs /. subst)
  (cx, rs) /. (R restr) = (cx, rs +. restr)

instance APPLY Clash Subst where
  (l :=: r) /. subst = (l /. subst) :=: (r /. subst)

instance APPLY Clash Contr where
  clash /. (S subst) = clash /. subst
  clash /. (R restr) = clash
