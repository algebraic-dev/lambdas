module Type.BiSimple where

import Control.Monad.Except (MonadError)
import Data.Map (Map)
import Data.Set (Set)
import Util     (blue)

import qualified Type.Utils.Expr      as Expr
import qualified Data.Map             as Map
import qualified Data.Set             as Set
import qualified Control.Monad.Except as Except

-- Implementation of a type checker for simply typed lambda calculus
-- based on https://arxiv.org/pdf/1908.05839.pdf. Simply typed lambda
-- calculus dont have polymorphic things so it's an straightforward
-- implementation without existentials, markers and shit like that.

-- The monad that will help with error handling to the REPL
type Typer m = MonadError String m

type Id = String

----------------------------------------------------------------
--                                                            --
--   Fig. 1. A simply typed 𝜆-calculus (: judgment) and a     --
--       bidirectional version (⇒ and ⇐ judgments)           --
--                                                            --
----------------------------------------------------------------

-- Here we have three types of types that includes a simple type "alpha"
-- that is the name of a type like "String" or "Int", Arrows that are
-- functions type like (Int -> String) and Pairs that are tuples.

-- Added pairs and removed the unit rule because they're better to illustrate
-- some real types

-- 𝐴, 𝐵, 𝐶 ::= α | 𝐴 → 𝐴 | A × A
data Ty = TyAlpha Id | TyArrow Ty Ty | TyPair Ty Ty deriving Eq

instance Show Ty where
    show = \case
      TyAlpha s                 -> blue s
      TyArrow ty@TyArrow {} ty' -> concat ["(", show ty, ") -> ", show ty']
      TyArrow ty ty'            -> concat [show ty, " -> ", show ty']
      TyPair a b                -> show a ++ " × " ++ show b

-- The context will store all the variables and types that exists in this
-- context.

-- Γ ::= · | Γ, 𝑥 : 𝐴
data Context = Context { ctxVars :: Map Id Ty, ctxTypes :: Set Id }

newVar :: Context -> Id -> Ty -> Context
newVar ctx name ty = ctx { ctxVars = Map.insert name ty (ctxVars ctx) }

simpleCtx :: Context
simpleCtx = Context Map.empty (Set.fromList ["Int", "String"])

-- 𝑒 ::= 𝑥 | 𝜆𝑥 . 𝑒 | 𝑒 𝑒 | ()
-- Expressions / Lambda calculus with some things

type Expr = Expr.VExpr Ty

-- We check if the type is well formed under the context
typeWellFormed :: Context -> Ty -> Bool
typeWellFormed ctx = \case
  TyAlpha id -> Set.member id (ctxTypes ctx)
  TyArrow ty ty' -> typeWellFormed ctx ty && typeWellFormed ctx ty'
  TyPair ty ty' -> typeWellFormed ctx ty && typeWellFormed ctx ty'

unify :: Typer m => Context -> Ty -> Ty -> m Context
unify ctx a b =
  if a == b
    then pure ctx
    else Except.throwError $ "Cannot unify types '" ++ show a ++ "' and '" ++ show b ++ "'"

-- Synthetizes a type from expressions
typeSynth :: Typer m => Context -> Expr -> m (Context, Ty)
typeSynth ctx = \case
  Expr.Var s -> -- Var⇒
    case Map.lookup s (ctxVars ctx) of
      Just r -> pure (ctx, r)
      Nothing -> Except.throwError $ "Cannot find variable '" ++ s ++ "'"
  Expr.App ve ve' -> do -- →E⇒
    (newCtx, funTy) <- typeSynth ctx ve
    case funTy of
      TyArrow from to -> do
        lastestCtx <- typeCheck newCtx ve' from
        pure (lastestCtx, to)
      _ -> Except.throwError $ "Cannot use type '" ++ show funTy ++ "' as a function!"
  Expr.Ann ve ty -> -- Anno⇒
    if typeWellFormed ctx ty
      then do ctx' <- typeCheck ctx ve ty
              pure (ctx', ty)
      else Except.throwError ("Malformed type '" ++ show ty ++ "'")
  Expr.EPair a b -> do -- Pair⇒ (Extra :0)
    (ctx', tyA)  <- typeSynth ctx a
    (ctx'', tyB) <- typeSynth ctx' b
    pure (ctx'', TyPair tyA tyB)
  Expr.EStr s -> pure (ctx, TyAlpha "String") -- Extra
  Expr.EInt s -> pure (ctx, TyAlpha "Int") -- Extra
  expr -> Except.throwError ("Cannot synthetize a type for '" ++ show expr ++ "' plz put an annotation!")

typeCheck :: Typer m => Context -> Expr -> Ty -> m Context
typeCheck ctx expr ty = case (expr, ty) of
    (Expr.Lam binder body, TyArrow from to) -> do -- →I⇐
      typeCheck (newVar ctx binder from) body to
    (e, b) -> do -- Sub⇐
      (ctx', ty) <- typeSynth ctx e
      unify ctx' ty b

runInference :: Expr -> Either String Ty
runInference = fmap snd . Except.runExcept . typeSynth simpleCtx