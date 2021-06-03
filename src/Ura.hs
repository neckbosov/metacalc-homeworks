module Ura where

import AST
import Classes
import Data.List ((\\))
import Env
import ProcessTree
import Restrictions
import Substitutions
import Unify

type TLevel = [(Class, Tree)]

type Tab = [(Class, CExp)]

tab :: Prog -> Class -> Tab
tab p x = tab' [(x, tree)] []
  where
    tree = xptr p x

tab' :: TLevel -> TLevel -> Tab
tab' ((xi, LEAF c) : lv1) lv2 = (xi, cex) : tab' lv1 lv2
  where
    ((RETURN exp, ce), _) = c
    cex = exp /. ce
tab' ((xi, NODE _ bs) : lv1) lv2 = tab' lv1 lv2'
  where
    lv2' = tabB xi bs lv2
tab' [] [] = []
tab' [] lv2 = tab' lv2 []

tabB :: Class -> [Branch] -> TLevel -> TLevel
tabB xi ((cnt, tree) : bs) lv = tabB xi bs ((xi /. cnt, tree) : lv)
tabB xi [] lv = lv

ura' :: Prog -> Class -> EVal -> Classes
ura' p x = urac (tab p x)

urac :: Tab -> EVal -> Classes
urac ((xi, cex) : ptab') y =
  case unify [cex] [y] of
    (False, _) -> tail
    (True, s) -> case xi' of
      (_, INCONSISTENT) -> tail
      _ -> xi' : tail
      where
        xi' = xi /. s
  where
    tail = urac ptab' y
urac [] y = []

ura :: Prog -> Class -> EVal -> [(Subst, Restr)]
ura p x y = map altRepr (ura' p x y)
  where
    altRepr :: Class -> (Subst, Restr)
    altRepr xi = subClassCntr x xi

subClassCntr :: Class -> Class -> (Subst, Restr)
subClassCntr (ces, r) (cesi, ri) = (ress, resr)
  where
    (True, ress) = unify ces cesi
    resr = case ri of
      INCONSISTENT -> INCONSISTENT
      RESTR rsi -> case r of
        INCONSISTENT -> RESTR rsi
        RESTR rs -> RESTR $ rsi \\ (rs /. ress)