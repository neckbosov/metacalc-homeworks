module ProcessTree where

import AST
import Classes
import Env
import Restrictions
import Substitutions

type FreeIndex = Int

freeindex :: FreeIndex -> Class -> FreeIndex
freeindex i c = 1 + maximum (i : map index (cvars c))
  where
    index :: CVar -> Int
    index (CVA i) = i
    index (CVE i) = i

mkCAVar, mkCEVar :: FreeIndex -> (CVar, FreeIndex)
mkCEVar i = (CVE i, i + 1)
mkCAVar i = (CVA i, i + 1)

splitA :: CVar -> CExp -> Split
splitA cv@(CVA _) caexp = (S [cv :-> caexp], R (RESTR [cv :=/=: caexp]))

splitE :: CVar -> FreeIndex -> (Split, FreeIndex)
splitE cv@(CVE _) i = ((S [cv :-> CONS cvh cvt], S [cv :-> cva]), i')
  where
    (cvh, i1) = mkCEVar i
    (cvt, i2) = mkCEVar i1
    (cva, i') = mkCAVar i2

data Tree = LEAF Conf | NODE Conf [Branch]
  deriving (Show)

type Branch = (Contr, Tree)

ptr :: Prog -> Class -> Tree
ptr p cl@(ces, r) = evalT c p i
  where
    (DEFINE f prms _) : p' = p
    ce = mkEnv prms ces
    c = ((CALL f prms, ce), r)
    i = freeindex 0 cl

evalT :: Conf -> Prog -> FreeIndex -> Tree
evalT c@((CALL f args, ce), r) p i =
  NODE c [(idC, evalT c' p i)]
  where
    DEFINE _ prms t' = getDef f p
    ce' = mkEnv prms (args /. ce)
    c' = ((t', ce'), r)
evalT c@((ALT cnd t1 t2, ce), r) p i =
  NODE c [(cnt1, evalT c1' p i'), (cnt2, evalT c2' p i')]
  where
    ((cnt1, cnt2), uce1, uce2, i') = ccond cnd ce i
    ((_, ce1), r1) = c /. cnt1
    c1' = ((t1, ce1 +. uce1), r1)
    ((_, ce2), r2) = c /. cnt2
    c2' = ((t2, ce2 +. uce2), r2)
evalT c@((RETURN exp, ce), r) p i = LEAF c

ccond :: Cond -> CEnv -> FreeIndex -> (Split, CEnv, CEnv, FreeIndex)
ccond (EQA' x y) ce i =
  let x' = x /. ce; y' = y /. ce
   in case (x', y') of
        (a, b) | a == b -> ((idC, emptC), [], [], i)
        (ATOM a, ATOM b) -> ((emptC, idC), [], [], i)
        (CVA _, a) -> (splitA x' a, [], [], i)
        (a, CVA _) -> (splitA y' a, [], [], i)
ccond (CONS' x vh vt va) ce i =
  let x' = x /. ce
   in case x' of
        CONS h t -> ((idC, emptC), [vh := h, vt := t], [], i)
        ATOM a -> ((emptC, idC), [], [va := x'], i)
        CVA _ -> ((emptC, idC), [], [va := x'], i)
        CVE _ -> (split, [vh := ch, vt := ct], [va := ca], i')
          where
            (split, i') = splitE x' i
            (S [_ :-> (CONS ch ct)], S [_ :-> ca]) = split

xptr' :: Prog -> Class -> Tree
xptr' p cl@(ces, r) = xevalT c p i
  where
    (DEFINE f prms _) : p' = p
    ce = mkEnv prms ces
    c = ((CALL f prms, ce), r)
    i = freeindex 0 cl

xevalT :: Conf -> Prog -> FreeIndex -> Tree
xevalT c@((CALL f args, ce), r) p i = case cutBranches [(idC, evalT c' p i)] of
  [] -> LEAF invalidConf
  brs -> NODE c brs
  where
    DEFINE _ prms t' = getDef f p
    ce' = mkEnv prms (args /. ce)
    c' = ((t', ce'), r)
xevalT c@((ALT cnd t1 t2, ce), r) p i = case cutBranches [(cnt1, evalT c1' p i'), (cnt2, evalT c2' p i')] of
  [] -> LEAF invalidConf
  brs -> NODE c brs
  where
    ((cnt1, cnt2), uce1, uce2, i') = ccond cnd ce i
    ((_, ce1), r1) = c /. cnt1
    c1' = ((t1, ce1 +. uce1), r1)
    ((_, ce2), r2) = c /. cnt2
    c2' = ((t2, ce2 +. uce2), r2)
xevalT c@((RETURN exp, ce), r) p i = LEAF c

invalidConf :: Conf
invalidConf = ((RETURN (ATOM "kek"), []), INCONSISTENT)

cutBranches :: [Branch] -> [Branch]
cutBranches [] = []
cutBranches (b@(cnt, tree) : bs) =
  case tree of
    LEAF (_, INCONSISTENT) -> cutBranches bs
    NODE (_, INCONSISTENT) _ -> cutBranches bs
    _ -> b : cutBranches bs

xptr :: Prog -> Class -> Tree
xptr p cl = NODE c (cutT brs)
  where
    tree = ptr p cl
    NODE c brs = tree

cutT :: [Branch] -> [Branch]
cutT [] = []
cutT (b@(cnt, tree) : bs) =
  case tree of
    LEAF (_, INCONSISTENT) -> cutT bs
    NODE (_, INCONSISTENT) _ -> cutT bs
    LEAF c -> b : cutT bs
    NODE c bs' -> b' : cutT bs
      where
        tree' = NODE c (cutT bs')
        b' = (cnt, tree')
