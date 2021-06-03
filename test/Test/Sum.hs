module Test.Sum where

import AST
import Arith
import Interpretator
import Test.Tasty.HUnit (Assertion, assertBool, (@?=))

numToExp :: Int -> Exp -> Exp
numToExp 0 rest = CONS (ATOM "0") rest
numToExp 1 rest = CONS (ATOM "1") rest
numToExp n rest = let r = n `mod` 2 in CONS (ATOM (show r)) rest

expToNum :: Exp -> Int -> Int
expToNum (ATOM _) acc = acc
expToNum (CONS (ATOM s) rest) acc = let x = read s :: Int in expToNum rest (acc * 2 + x)
expToNum _ _ = undefined

unit_sum_simple :: Assertion
unit_sum_simple = int tsgSumProg [CONS (ATOM "1") (ATOM ""), CONS (ATOM "1") (ATOM "")] @?= CONS (ATOM "1") (CONS (ATOM "0") (ATOM ""))

unit_sum_harder :: Assertion
unit_sum_harder = int tsgSumProg [numToExp 26 (ATOM ""), numToExp 35 (ATOM "")] @?= numToExp 61 (ATOM "")