module Expr where

data Expr ty
  = Var String
  | Lam String (Expr ty)
  | App (Expr ty) (Expr ty)
  | Ann (Expr ty) ty