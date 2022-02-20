module Expr where 

data VExpr ty
  = Var    String
  | Lam    String (VExpr ty)
  | App    (VExpr ty) (VExpr ty)
  | Ann    (VExpr ty) ty
  | EStr   String 
  | EPair  (VExpr ty) (VExpr ty)
  | EInt   Int

instance Show t => Show (VExpr t) where 
  show = \case 
    Var s -> s
    Lam s ve -> "(λ " ++ s ++ "." ++ show ve ++ ")"
    App ve ve' -> "(" ++ show ve ++ " " ++ show ve' ++ ")"
    Ann ve t -> "(" ++ show ve ++ " : " ++ show t ++ ")"
    EStr s -> show s
    EInt n -> show n
    EPair a b -> show a ++ " × " ++ show b
