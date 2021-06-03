module Interpretator where

import AST
import Data.List
import qualified Data.Map.Strict as Map
import Env

idProg :: Prog
idProg =
  [ DEFINE
      "Id"
      [e'x]
      (RETURN e'x)
  ]
  where
    e'x = PVE "x"

int :: Prog -> [EVal] -> EVal
int p d = eval s p
  where
    (DEFINE f prms _) : p' = p
    e = mkEnv prms d
    s = (CALL f prms, e)

eval :: State -> Prog -> EVal
eval s@(CALL f args, e) p = eval s' p
  where
    DEFINE _ prms t' = getDef f p
    e' = mkEnv prms (args /. e)
    s' = (t', e')
eval s@(ALT c t1 t2, e) p = case cond c e of
  TRUE ue -> eval (t1, e +. ue) p
  FALSE ue -> eval (t2, e +. ue) p
eval s@(RETURN exp, e) p = exp /. e

data CondRes = TRUE Env | FALSE Env
  deriving (Show)

cond :: Cond -> Env -> CondRes
cond (EQA' x y) e =
  let x' = x /. e; y' = y /. e
   in case (x', y') of
        (ATOM a, ATOM b) | a == b -> TRUE []
        (ATOM a, ATOM b) -> FALSE []
cond (CONS' x vh vt va) e =
  let x' = x /. e
   in case x' of
        CONS h t -> TRUE [vh := h, vt := t]
        ATOM a -> FALSE [va := x']

match_prog :: Prog
match_prog =
  [ DEFINE
      "Match"
      [e_substr, e_string]
      (CALL "CheckPos" [e_substr, e_string, e_substr, e_string]),
    DEFINE
      "NextPos"
      [e_substring, e_string]
      ( ALT
          (CONS' e_string e__ e_string_tail a__)
          (CALL "Match" [e_substring, e_string_tail])
          (RETURN _failResURE)
      ),
    DEFINE
      "CheckPos"
      [e_subs, e_str, e_substring, e_string]
      ( ALT
          (CONS' e_subs e_subs_head e_subs_tail a__)
          ( ALT
              (CONS' e_subs_head e__ e__ a_subs_head)
              (RETURN _failResURE)
              ( ALT
                  (CONS' e_str e_str_head e_str_tail a__)
                  ( ALT
                      (CONS' e_str_head e__ e__ a_str_head)
                      (RETURN _failResURE)
                      ( ALT
                          (EQA' a_subs_head a_str_head)
                          ( CALL
                              "CheckPos"
                              [ e_subs_tail,
                                e_str_tail,
                                e_substring,
                                e_string
                              ]
                          )
                          (CALL "NextPos" [e_substring, e_string])
                      )
                  )
                  (RETURN _failResURE)
              )
          )
          (RETURN _SUCCESS)
      )
  ]
  where
    e_substr = PVE "substr"
    e_string = PVE "string"
    e_string_tail = PVE "e_string_tail"
    e_substring = PVE "substring"
    e__ = PVE "_"
    e_string - tail = PVE "string-tail"
    a__ = PVA "_"
    e_subs = PVE "subs"
    e_str = PVE "str"
    a_subs_head = PVA "subs_head"
    e_subs_head = PVE "subs_head"
    e_subs_tail = PVE "subs_tail"
    a_str_head = PVA "str_head"
    e_str_head = PVE "str_head"
    e_str_tail = PVE "str_tail"
    _failResURE = ATOM "_failResURE"
    _SUCCESS = ATOM "_SUCCESS"
