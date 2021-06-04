module Arith where

import AST

reverseDef :: FDef
reverseDef = DEFINE "Reverse" [PVE "str"] (CALL "ReverseRec" [PVE "str", ATOM ""])

reverseRec :: FDef
reverseRec =
  DEFINE
    "ReverseRec"
    [e_str, e_res]
    ( ALT
        (CONS' e_str e_subs_head e_subs_tail a__)
        (CALL "ReverseRec" [e_subs_tail, CONS e_subs_head e_res])
        (RETURN e_res)
    )
  where
    e_str = PVE "str"
    e_res = PVE "res"
    a__ = PVA "_"
    e_subs_head = PVE "subs_head"
    e_subs_tail = PVE "subs_tail"

reverseProg = [reverseDef, reverseRec]

digitsSum :: FDef
digitsSum =
  DEFINE
    "DigitsSum"
    [dig1, dig2]
    ( ALT
        (EQA' dig1 one)
        ( ALT
            (EQA' dig2 one)
            (RETURN (CONS zero one))
            ( ALT
                (EQA' dig2 zero)
                (RETURN (CONS one zero))
                (RETURN _fail)
            )
        )
        ( ALT
            (EQA' dig1 zero)
            ( ALT
                (EQA' dig2 one)
                (RETURN (CONS one zero))
                ( ALT
                    (EQA' dig2 zero)
                    (RETURN (CONS zero zero))
                    (RETURN _fail)
                )
            )
            (RETURN _fail)
        )
    )
  where
    dig1 = PVA "dig1"
    dig2 = PVA "dig2"
    one = ATOM "1"
    zero = ATOM "0"
    _fail = ATOM "FAILURE"

tsgSum :: FDef
tsgSum = DEFINE "Sum" [num1, num2] (CALL "ReverseAndSum" [num1, num2, ATOM "", ATOM ""])
  where
    num1 = PVE "num1"
    num2 = PVE "num2"

tsgReverseAndSum :: FDef
tsgReverseAndSum =
  DEFINE
    "ReverseAndSum"
    [num1, num2, r1, r2]
    ( ALT
        (CONS' num1 dig1 rest1 a__)
        (CALL "ReverseAndSum" [rest1, num2, CONS dig1 r1, r2])
        ( ALT
            (CONS' num2 dig2 rest2 a__)
            (CALL "ReverseAndSum" [num1, rest2, r1, CONS dig2 r2])
            (CALL "SumImp" [r1, r2, ATOM "", ATOM "0"])
        )
    )
  where
    num1 = PVE "num1"
    num2 = PVE "num2"
    r1 = PVE "r1"
    r2 = PVE "r2"
    dig1 = PVE "dig"
    rest1 = PVE "rest1"
    dig2 = PVE "dig2"
    rest2 = PVE "rest2"
    a__ = PVA "_"

tsgSumImp :: FDef
tsgSumImp =
  DEFINE
    "SumImp"
    [num1, num2, res, mv]
    ( ALT
        (CONS' num1 edig1 erest1 a__)
        ( ALT
            (CONS' edig1 e1_ e2_ dig1)
            (RETURN _fail)
            ( ALT
                (CONS' num2 edig2 erest2 a__)
                ( ALT
                    (CONS' edig2 e1_ e2_ dig2)
                    (RETURN _fail)
                    (CALL "SumWithDigits" [dig1, dig2, erest1, erest2, res, mv])
                )
                (CALL "SumWithMove" [num1, mv, res])
            )
        )
        ( ALT
            (CONS' num2 edig2 erest2 a__)
            ( ALT
                (CONS' edig2 e1_ e2_ dig2)
                (RETURN _fail)
                (CALL "SumWithMove" [num2, mv, res])
            )
            ( ALT
                (EQA' mv (ATOM "1"))
                (RETURN (CONS (ATOM "1") res))
                (RETURN res)
            )
        )
    )
  where
    num1 = PVE "num1"
    num2 = PVE "num2"
    dig1 = PVA "dig1"
    dig2 = PVA "dig2"
    edig1 = PVE "edig1"
    edig2 = PVE "edig2"
    erest1 = PVE "erest1"
    erest2 = PVE "erest2"
    res = PVE "res"
    mv = PVA "mv"
    a__ = PVA "_"
    e1_ = PVE "e1_"
    e2_ = PVE "e2_"
    _fail = ATOM "FAILURE"

tsgSumWithMove :: FDef
tsgSumWithMove =
  DEFINE
    "SumWithMove"
    [num, mv, res]
    ( ALT
        (CONS' num edig erest a__)
        ( ALT
            (CONS' edig e1_ e2_ dig)
            (RETURN _fail)
            ( ALT
                (EQA' dig one)
                ( ALT
                    (EQA' mv one)
                    (CALL "SumWithMove" [erest, one, CONS zero res])
                    (CALL "SumWithMove" [erest, zero, CONS one res])
                )
                ( ALT
                    (EQA' dig zero)
                    ( ALT
                        (EQA' mv one)
                        (CALL "SumWithMove" [erest, zero, CONS one res])
                        (CALL "SumWithMove" [erest, zero, CONS zero res])
                    )
                    (RETURN _fail)
                )
            )
        )
        ( ALT
            (EQA' mv one)
            (RETURN (CONS one res))
            (RETURN res)
        )
    )
  where
    num = PVE "num"
    mv = PVA "mv"
    res = PVE "res"
    edig = PVE "edig"
    dig = PVA "dig"
    erest = PVE "erest"
    a__ = PVA "_"
    e1_ = PVE "e1_"
    e2_ = PVE "e2_"
    _fail = ATOM "FAILURE"
    one = ATOM "1"
    zero = ATOM "0"

tsgSumWithDigits :: FDef
tsgSumWithDigits =
  DEFINE
    "SumWithDigits"
    [dig1, dig2, num1, num2, res, mv]
    ( ALT
        (EQA' dig1 one)
        ( ALT
            (EQA' dig2 one)
            (CALL "SumImp" [num1, num2, CONS mv res, one])
            ( ALT
                (EQA' dig2 zero)
                ( ALT
                    (EQA' mv one)
                    (CALL "SumImp" [num1, num2, CONS zero res, one])
                    (CALL "SumImp" [num1, num2, CONS one res, zero])
                )
                (RETURN _fail)
            )
        )
        ( ALT
            (EQA' dig1 zero)
            ( ALT
                (EQA' dig2 one)
                ( ALT
                    (EQA' mv one)
                    (CALL "SumImp" [num1, num2, CONS zero res, one])
                    (CALL "SumImp" [num1, num2, CONS one res, zero])
                )
                ( ALT
                    (EQA' dig2 zero)
                    ( ALT
                        (EQA' mv one)
                        (CALL "SumImp" [num1, num2, CONS one res, zero])
                        (CALL "SumImp" [num1, num2, CONS zero res, zero])
                    )
                    (RETURN _fail)
                )
            )
            (RETURN _fail)
        )
    )
  where
    num1 = PVE "num1"
    num2 = PVE "num2"
    dig1 = PVA "dig1"
    dig2 = PVA "dig2"
    edig1 = PVE "edig1"
    edig2 = PVE "edig2"
    erest1 = PVE "erest1"
    erest2 = PVE "erest2"
    res = PVE "res"
    mv = PVA "mv"
    a__ = PVA "_"
    e1_ = PVE "e1_"
    e2_ = PVE "e2_"
    _fail = ATOM "FAILURE"
    one = ATOM "1"
    zero = ATOM "0"

tsgSumProg :: Prog
tsgSumProg = [tsgSum, tsgReverseAndSum, tsgSumImp, tsgSumWithDigits, tsgSumWithMove]

numToExp :: Int -> Exp -> Exp
numToExp 0 rest = CONS (ATOM "0") rest
numToExp 1 rest = CONS (ATOM "1") rest
numToExp n rest = let r = n `mod` 2 in numToExp (n `div` 2) (CONS (ATOM $ show r) rest)

expToNum :: Exp -> Int -> Int
expToNum (ATOM _) acc = acc
expToNum (CONS (ATOM s) rest) acc = let x = read s :: Int in expToNum rest (acc * 2 + x)
expToNum _ _ = undefined
