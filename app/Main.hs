module Main where

import AST
import Arith
import Data.List
import Interpretator
import Lib

main :: IO ()
main = do
  s <- getLine
  let ws = words s
  let a = head ws
  let b = head (tail ws)
  let x = read a :: Int
  let y = read b :: Int
  let ex = numToExp x (ATOM "")
  let ey = numToExp y (ATOM "")
  print (expToNum (int tsgSumProg [ex, ey]) 0)
