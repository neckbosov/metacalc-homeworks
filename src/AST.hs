module AST where

data Exp
  = ATOM Atom
  | PVA VName
  | PVE VName
  | CVA Int
  | CVE Int
  | CONS Exp Exp
  deriving (Eq, Show)

type Atom = String

type AVar = Exp

type EVar = Exp

type Parm = Exp

type EVal = Exp

type AVal = Exp

type Var = Exp

type AExp = Exp

type Prog = [FDef]

type FName = String

type VName = String

data FDef = DEFINE FName [Parm] Term
  deriving (Show)

data Term
  = ALT Cond Term Term
  | CALL FName [Exp]
  | RETURN Exp
  deriving (Show)

data Cond
  = EQA' AExp AExp
  | CONS' Exp EVar EVar AVar
  deriving (Show)


getDef :: FName -> Prog -> FDef
getDef fn p = head [fd | fd@(DEFINE f _ _) <- p, f == fn]