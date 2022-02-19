module Main where

import Dunfield ( Ty(TyAlpha, TyForall, TyFun), Kind(..), runInference )
import Expr ( VExpr(EInt, Ann, Lam, App, Var, EStr) )
import Data.Foldable (for_)
import Util (red)

id' :: Ty 'Poly
id' = TyForall "a" (TyFun (TyAlpha "a") (TyAlpha "a"))

expr :: VExpr (Ty 'Poly)
expr =  Ann (Lam "b" (App (Var "b") (EStr "ata"))) (TyFun id' (TyAlpha "String"))

main :: IO ()
main = either (putStrLn . (red "Error: " ++)) print (runInference expr)
