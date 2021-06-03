module Unify where

import AST
import Restrictions
import Substitutions

type UnifRes = (Bool, Subst)

failRes :: UnifRes
failRes = (False, [])

data Clash = CExp :=: CExp
  deriving (Show)

type Clashes = [Clash]

unify :: CExps -> CExps -> UnifRes
unify ces1 ces2
  | length ces1 /= length ces2 = failRes
  | otherwise = unify' [] chs
  where
    chs = zipWith (:=:) ces1 ces2

unify' :: Clashes -> Clashes -> UnifRes
unify' rchs [] = (True, subst)
  where
    subst = map (\(a :=: b) -> a :-> b) rchs
unify' rchs chs@(ch : chs') =
  case ch of
    ATOM a :=: ATOM b | a == b -> unify' rchs chs'
    ATOM a :=: cex -> failRes
    cvar@(CVA _) :=: caex@(ATOM _) -> moveCl rchs chs
    cvar@(CVA _) :=: caex@(CVA _) -> moveCl rchs chs
    cvar@(CVA _) :=: cex -> failRes
    cvar@(CVE _) :=: cex -> moveCl rchs chs
    CONS a1 b1 :=: CONS a2 b2 -> unify' rchs (p ++ chs')
      where
        p = [a1 :=: a2, b1 :=: b2]
    CONS a1 b1 :=: cex -> failRes

moveCl :: Clashes -> Clashes -> UnifRes
moveCl rchs chs@(ch@(cvar :=: cexp) : chs') =
  case [y | (x :=: y) <- rchs, x == cvar] of
    [] -> unify' (ch : rchs) chs'
    [y] | y == cexp -> unify' rchs chs'
    [y] | otherwise -> failRes