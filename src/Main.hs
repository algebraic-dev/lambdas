module Main where

import Dunfield

main :: IO ()
main = print $ runInference (Lam "a" (Lam "b" (App (Var "b") (App (Var "a") (Var "b")))))
