module Dunfield where

import Data.Maybe (fromJust, isJust, catMaybes, mapMaybe)
import Data.Function (on)
import Data.List (nub, delete)

-- A simple implementation of the paper "Complete and Easy Bidirectional 
-- Typechecking for Higher-Rank Polymorphism". I'm writing this to understand 
-- it better. I want to be able to modify it soon lol so i'll have to explain it 
-- to other to see if they can understand it too.

type Id = String

-- Polymorphic types are types that can have "multiple forms" like the identity function
-- that can receive "any" type and return the *same* "any" type. We can express the 
-- identity function type as "∀α. α -> α" where α is the type being binded and will be 
-- substituted in the body when instantiated. In some languages it's called "generics"

-------------------------------------------------------------------------------------
--
-- Figure 6. Syntax of types, monotypes, and contexts in the algorithmic system
--
-------------------------------------------------------------------------------------

data Kind = Poly | Mono

-- Mono and poly types together
data Ty :: Kind -> * where
  TyAlpha  :: Id -> Ty a                 -- α      (Simple types)
  TyExists :: Id -> Ty a                 -- ^α     (Existential type / Not discovered yet)
  TyFun    :: Ty a -> Ty a -> Ty a       -- A → B  (Function that maps from A to B)
  TyForall :: Id -> Ty 'Poly -> Ty 'Poly -- ∀α. A  (Universal quantification over types / Generics binding)

-- Deriving Eq for Type :) with Standalone Deriving
deriving instance Eq (Ty a)

-- Elements that will be inside the context 
data CtxElem
  = ElTy     Id             -- α       (Types that exists)
  | ElVar    Id (Ty 'Poly)  -- x : A   (Type of a variable x)
  | ElExists Id             -- ^α      (Exists the existential ^α)
  | ElSolved Id (Ty 'Mono)  -- ^α = τ  (The existential ^α is the same as t)
  | ElMarker Id             -- ▶^α     (Useful for scoping rules)
  deriving Eq

-- Contexts have to be some kind of *ordered* data structure. It's essential in the type 
-- system in order to make scoping rules work under this system. Most of the rules in the paper
-- Are described using the *Hole Notation* that can be used to describe a lot of things like 

-- Γ[Θ]                             Exists an Θ in Γ
-- Γ[^a][^β] then Γ[^a][^β = ^α]    Enforce the order of substitutions

newtype Context = Context { ctxElems :: [CtxElem]}
  deriving (Semigroup, Monoid)

-- These functions are Context manipulation helpers

(<|) :: CtxElem -> Context -> Context
(<|) elem (Context ctx) = Context $ elem : ctx

getTy :: Context -> [Id]
getTy = mapMaybe (\case { ElTy i -> Just i; _ -> Nothing }) . ctxElems

getVars :: Context -> [Id]
getVars = mapMaybe (\case { ElVar i _ -> Just i; _ -> Nothing }) . ctxElems

getExistentials :: Context -> [Id]
getExistentials = mapMaybe (\case { ElSolved i _ -> Just i; ElExists i -> Just i; _ -> Nothing }) . ctxElems

getUnsolved :: Context -> [Id]
getUnsolved = mapMaybe (\case { ElExists i-> Just i; _ -> Nothing }) . ctxElems

getSolved :: Context -> [Id]
getSolved = mapMaybe (\case { ElSolved i _ -> Just i; _ -> Nothing }) . ctxElems

getMarkers :: Context -> [Id]
getMarkers = mapMaybe (\case { ElMarker i -> Just i; _ -> Nothing }) . ctxElems

findSolved :: Context -> Id -> Maybe (Ty 'Mono)
findSolved ctx name' = go (ctxElems ctx)
  where go (ElSolved x ty : _) | x == name' = Just ty
        go (_ : xs) = go xs 
        go [] = Nothing

-- Type manipulation helpers

toPoly :: Ty 'Mono -> Ty 'Poly 
toPoly = \case
  TyAlpha s -> TyAlpha s
  TyExists s -> TyExists s
  TyFun ty ty' -> TyFun (toPoly ty) (toPoly ty')

toMono :: Ty 'Poly -> Maybe (Ty 'Poly)
toMono = \case
  TyAlpha s -> Just $ TyAlpha s
  TyExists s -> Just $ TyExists s
  TyFun ty ty' -> TyFun <$> toMono ty <*> toMono ty'
  TyForall s ty -> Nothing

-- Substitute all the ids by the type in a type [^a/a]α
typeSubst :: Id -> Ty a -> Ty a -> Ty a 
typeSubst from to = \case
  TyAlpha s     | s == from -> to
                | otherwise -> TyAlpha s
  TyExists s    | s == from -> to
                | otherwise -> TyExists s
  TyForall s ty | s == from -> TyForall s ty  
                | otherwise -> TyForall s (typeSubst from to ty)
  TyFun ty ty' -> TyFun (typeSubst from to ty) (typeSubst from to ty')

-- Get all types that are not bound by universal quantification FV(t)
freeVars :: Ty a -> [Id]
freeVars = \case   
  TyAlpha s -> [s]
  TyExists s -> [s]
  TyFun ty ty' -> nub $ ((++) `on` freeVars) ty ty' 
  TyForall s ty -> s `delete` freeVars ty 

-------------------------------------------------------------------------------------
--
--   Figure 7. Well-formedness of types and contexts in the algorith-mic system
--                                     
-------------------------------------------------------------------------------------

-- Under a context Γ ⊢ A, type A is well formed
typeWellFormed :: Context -> Ty a -> Bool
typeWellFormed ctx = \case
  TyAlpha s     -> s `elem` getTy ctx -- UvarWF 
  TyExists s    -> s `elem` getExistentials ctx -- SolvedEvarWF / EvarWF
  TyFun ty ty'  -> typeWellFormed ctx ty && typeWellFormed ctx ty' -- ArrowWF
  TyForall s ty -> typeWellFormed (ElTy s <| ctx) ty -- ForallWF

-- Γ ctx Algorithmic context Γ is well-formed
ctxWellFormed :: Context -> Bool
ctxWellFormed (Context [])     = True -- 
ctxWellFormed (Context (x : xs)) =
    go (Context xs) x && ctxWellFormed (Context xs)
  where 
    go ctx' = \case
      ElTy _        -> x `notElem` xs -- UvarCtx
      ElVar x ty    -> x `notElem` getVars ctx' -- VarCtx
      ElExists s    -> s `notElem` getExistentials ctx' -- EvarCtx 
      ElSolved s ty -> s `notElem` getExistentials ctx' && typeWellFormed ctx' ty -- SolvedEvarCtx
      ElMarker s -> s `notElem` getMarkers ctx' && s `notElem` getExistentials ctx' -- MarkerCtx

-------------------------------------------------------------------------------------
--
-- Figure 8. Applying a context, as a substitution, to a type
--                                     
-------------------------------------------------------------------------------------

applyCtx :: Context -> Ty 'Poly -> Ty 'Poly 
applyCtx ctx (TyAlpha s) = TyAlpha s
applyCtx ctx (TyForall b ty) = TyForall b (applyCtx ctx ty) 
applyCtx ctx (TyFun ty ty') = TyFun (applyCtx ctx ty) (applyCtx ctx ty')
applyCtx ctx (TyExists s) = case findSolved ctx s of
  Nothing -> TyExists s
  Just ty -> toPoly ty

