module Test.Sum where

import AST
import Arith
import Interpretator
import Test.Tasty.HUnit (Assertion, assertBool, (@?=))

unit_sum_simple :: Assertion
unit_sum_simple = int tsgSumProg [CONS (ATOM "1") (ATOM ""), CONS (ATOM "1") (ATOM "")] @?= CONS (ATOM "1") (CONS (ATOM "0") (ATOM ""))

unit_sum_harder :: Assertion
unit_sum_harder = int tsgSumProg [numToExp 26 (ATOM ""), numToExp 35 (ATOM "")] @?= numToExp 61 (ATOM "")