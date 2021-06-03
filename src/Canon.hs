module Canon where

import AST
import Classes
import Data.List
import qualified Data.Map.Strict as Map
import Env
import ProcessTree
import Restrictions
import Substitutions

addCVar :: (Map.Map CVar CVar, Int) -> CExp -> (Map.Map CVar CVar, Int)
addCVar (renamings, id) (CVA i) | Nothing <- Map.lookup (CVA i) renamings = (Map.insert (CVA i) (CVA id) renamings, id + 1)
addCVar (renamings, id) (CVE i) | Nothing <- Map.lookup (CVE i) renamings = (Map.insert (CVE i) (CVE id) renamings, id + 1)
addCVar p _ = p

addCExp :: (Map.Map CVar CVar, Int) -> CExp -> (Map.Map CVar CVar, Int)
addCExp p cexp = foldl addCVar p (cvars cexp)

getRenamingSubst :: Int -> CExps -> Subst
getRenamingSubst id cexps = let substMap = fst $ foldl addCExp (Map.empty, id) cexps in map (uncurry (:->)) (Map.toList substMap)

instance Ord Exp where
  compare (PVA _) _ = undefined
  compare (PVE _) _ = undefined
  compare _ (PVA _) = undefined
  compare _ (PVE _) = undefined
  compare (ATOM a) (ATOM b) = compare a b
  compare (ATOM _) (CVA _) = GT
  compare (ATOM _) (CVE _) = GT
  compare (ATOM _) (CONS _ _) = LT
  compare (CVA _) (ATOM _) = LT
  compare (CVA i) (CVA j) = compare i j
  compare (CVA i) (CVE j) = compare i j
  compare (CVA _) (CONS _ _) = LT
  compare (CVE _) (ATOM _) = LT
  compare (CVE i) (CVA j) = compare i j
  compare (CVE i) (CVE j) = compare i j
  compare (CVE _) (CONS _ _) = LT
  compare (CONS _ _) (ATOM _) = GT
  compare (CONS _ _) (CVE _) = GT
  compare (CONS _ _) (CVA _) = GT
  compare (CONS r s) (CONS p q) = case compare r p of
    EQ -> compare s q
    res -> res

instance Ord InEq where
  compare (x1 :=/=: y1) (x2 :=/=: y2) = case compare x1 x2 of
    EQ -> compare y1 y2
    res -> res

decRen :: Int -> CVar -> SBind
decRen id (CVA i) = CVA i :-> CVA (i - id)
decRen id (CVE i) = CVE i :-> CVE (i - id)
decRen _ _ = undefined

canon :: Class -> Class
canon cl@(cexps, restr) = (newCes, newRes)
  where
    id0 = freeindex 0 cl
    rens = getRenamingSubst id0 cexps
    ces1 = cexps /. rens
    res1 = case restr of
      INCONSISTENT -> INCONSISTENT
      RESTR ineqs -> RESTR (ineqs /. rens)
    ren2 = map (decRen id0) (cvars (ces1, res1))
    newCes = ces1 /. ren2
    newRes = case res1 of
      INCONSISTENT -> INCONSISTENT
      RESTR ineqs -> RESTR ((nub . sort) $ ineqs /. rens)

-- additionaInEqs :: Class -> [InEq]
-- additionaInEqs (ces, restr) =
--   let allInEqs = map (uncurry (:=/=:)) $ filter (uncurry (/=)) ([(x, y) | x <- cvs, y <- cvs])
--    in case restr of
--         INCONSISTENT -> []
--         RESTR restrs -> filter (`notElem` restrs) allInEqs
--   where
--     cvs = cvars ces

-- createSBinds :: (CExp, Int) -> [SBind]
-- createSBinds a = undefined

-- rawSuperClasses :: Class -> Classes
-- rawSuperClasses = undefined

-- superClasses :: Class -> Classes
-- superClasses cl = nub $ map canon (rawSuperClasses cl)
