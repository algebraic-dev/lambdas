module Dunfield where

import Data.Maybe (fromJust, isJust, catMaybes, mapMaybe, fromMaybe)
import Data.Function (on)
import Data.List (nub, delete)
import Control.Monad.State (MonadState, get, state, replicateM, evalState)
import Data.Char (chr)

-- A simple implementation of the paper "Complete and Easy Bidirectional 
-- Typechecking for Higher-Rank Polymorphism". I'm writing this to understand 
-- it better and to explain it to my friends. 

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

instance Show (Ty a) where
    show = \case
      TyAlpha s -> s
      TyExists s -> '^' : s
      TyFun ty@TyFun {} ty' -> concat ["(", show ty, ") -> ", show ty']
      TyFun ty@TyForall {} ty' -> concat ["(", show ty, ") -> ", show ty']
      TyFun ty ty' -> concat [show ty, " -> ", show ty']
      TyForall s ty -> "∀ " ++ s ++ " . " ++ show ty

-- Deriving Eq for Type :) with Standalone Deriving
deriving instance Eq (Ty a)

-- Elements that will be inside the context 
-- An existential is used to state that there's a type that
-- we dont know the real type yet and we should use it to make some cool
-- assertions and bindings. The marker is useful to separate where each
-- part of the code should use which existential so it not goes out of it's scope.

data CtxElem
  = ElTy     Id             -- α       (Types that exists)
  | ElVar    Id (Ty 'Poly)  -- x : A   (Type of a variable x)
  | ElExists Id             -- ^α      (Exists the existential ^α)
  | ElSolved Id (Ty 'Mono)  -- ^α = τ  (The existential ^α is the same as t)
  | ElMarker Id             -- ▶^α     (Useful for scoping rules)
  deriving (Eq)

instance Show CtxElem where 
  show = \case
    ElTy s -> s
    ElVar s ty -> s ++ " : " ++ show ty 
    ElExists s -> "^" ++ s
    ElSolved s ty -> s ++ " = " ++ show ty
    ElMarker s -> "▶" ++ s

-- Contexts have to be some kind of *ordered* data structure. It's essential in this type 
-- checker in order to make scoping rules work. Most of the rules in the paper
-- Are described using the *Hole Notation* that can be used to describe a lot of things like 

-- Γ[Θ]                                                 Exists an Θ in sΓ
-- r[^b] = (a, ^b, ^c) then r[^b = a] = (a, ^b = a, ^c) Substitutions  
-- Γ[^a][^β] then Γ[^a][^β = ^α]                        Enforce the order of the substition of ^b to ^b = ^a


newtype Context = Context { ctxElems :: [CtxElem]}
  deriving (Semigroup, Monoid)

instance Show Context where 
  show (Context ct) = show ct  

-- Lambda calculus representantion
data Expr
  = Var String
  | Lam String Expr
  | App Expr Expr
  | Ann Expr (Ty 'Poly)

infixr 6 <|

-- These functions are Context manipulation helpers

(<|) :: CtxElem -> Context -> Context
(<|) elem (Context ctx) = Context $ elem : ctx

-- It drops the last part of the context until some ctxElem
-- for example, lets take the context [a : ^'a, ▶'a, ^'b]
-- if we drop the context until the Marker, then it will result in [^'b]

dropCtx :: CtxElem -> Context -> Context
dropCtx el (Context ctx) = Context $ go ctx
    where go [] = []
          go (x : xs) | el == x = xs
                      | otherwise = go xs

getTy :: Context -> [Id]
getTy (Context ctx) = [x | ElTy x <- ctx]

getVars :: Context -> [Id]
getVars (Context ctx) = [i | ElTy i <- ctx]

getExistentials :: Context -> [Id]
getExistentials = mapMaybe (\case { ElSolved i _ -> Just i; ElExists i -> Just i; _ -> Nothing }) . ctxElems

getUnsolved :: Context -> [Id]
getUnsolved (Context ctx) = [x | ElExists x <- ctx]

getSolved :: Context -> [Id]
getSolved (Context ctx) = [x | ElSolved x _ <- ctx]

getMarkers :: Context -> [Id]
getMarkers (Context ctx) = [x | ElMarker x <- ctx]

breakOn :: Context -> CtxElem  -> (Context, Context)
breakOn (Context ctx) el = let (l,r) = span (/= el) ctx in (Context l, Context $ tail r)

findSolved :: Context -> Id -> Maybe (Ty 'Mono)
findSolved ctx name' = go (ctxElems ctx)
  where go (ElSolved x ty : _) | x == name' = Just ty
        go (_ : xs) = go xs
        go [] = Nothing

findVar :: Context -> Id -> Maybe (Ty 'Poly)
findVar (Context ctx) name' = go ctx
  where go [] = Nothing
        go (ElVar x t : xs) | x == name' = Just t
                            | otherwise  = go xs
        go (x : xs) = go xs

isOrdered :: Context -> CtxElem -> CtxElem -> Bool
isOrdered (Context ctx) before after = go ctx
  where go [] = False
        go (x : xs) | x == after = True
                    | x == before = False
                    | otherwise = go xs

insertAt :: Context -> CtxElem -> [CtxElem] -> Context
insertAt ctx at elems = let (l, r) = breakOn ctx at in l <> (Context elems) <> r 

-- Solves a existential to a solved ctx var
solve :: Context -> Id -> Ty 'Mono -> Context
solve (Context ctx) id' ty = Context $ go ctx
  where go [] = []
        go (ElExists x : xs) | x == id' = ElSolved x ty : xs
        go (x : xs) = x : go xs

-- Type manipulation helpers

toPoly :: Ty 'Mono -> Ty 'Poly
toPoly = \case
  TyAlpha s -> TyAlpha s
  TyExists s -> TyExists s
  TyFun ty ty' -> TyFun (toPoly ty) (toPoly ty')

toMono :: Ty 'Poly -> Maybe (Ty 'Mono)
toMono = \case
  TyAlpha s -> Just $ TyAlpha s
  TyExists s -> Nothing -- Wrong definition of "monomorphic" but this function is helpful!
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

typeSubsts :: [(Id, Ty a)] -> Ty a -> Ty a
typeSubsts substs ty = foldl (flip $ uncurry typeSubst) ty substs

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
applyCtx ctx (TyAlpha s)     = TyAlpha s
applyCtx ctx (TyForall b ty) = TyForall b (applyCtx ctx ty)
applyCtx ctx (TyFun ty ty')  = TyFun (applyCtx ctx ty) (applyCtx ctx ty')
applyCtx ctx (TyExists s)    = case findSolved ctx s of
  Nothing -> TyExists s
  Just ty -> applyCtx ctx (toPoly ty)

numToStr :: Int -> [Char]
numToStr len | len <= 0 = []
             | otherwise = let (q, r) = (len-1) `quotRem` 26
                           in chr (97+r) : numToStr q

newName :: MonadState Int m => m String
newName = state (\s -> ('\'' : reverse (numToStr s), s+1))

----------------------------------------
--                                    --
--   Figure 9. Algorithmic subtyping  --
--                                    --
----------------------------------------

-- The algorthmic subtyping express the idea of A as a "subtype" of B t
-- to make it possible to transform a lower rank type to a higher rank 
-- by the process of subsumption.

-- Some rules are really simple like, a type A is subtype of himself
-- the same is applied to an existentials that have the same name.
-- Other rules are more complex and it leads to instantiation in both sides.

-- Γ ⊢ A <: B ⊣ ∆
subType :: MonadState Int m => Context -> Ty 'Poly -> Ty 'Poly -> m Context
subType ctx tyA tyB =
  case (tyA, tyB) of
    (TyAlpha x, TyAlpha y)   | x == y -> pure ctx -- <:Var
    (TyExists a, TyExists b) | a == b -> pure ctx -- <:Exvar
    (TyFun a a', TyFun b b') -> do -- <:→
      theta <- subType ctx b a
      delta <- subType theta (applyCtx theta a') (applyCtx theta b')
      pure ctx
    (TyForall b a', b')      -> do -- <:∀L
      alpha <- newName
      ctx'  <- subType (ElExists alpha <| ElMarker alpha <| ctx) (typeSubst b (TyExists alpha) a') b'
      pure (dropCtx (ElMarker alpha) ctx')
    (a', TyForall b b')      -> do -- <:∀R
      alpha <- newName
      subType (ElTy alpha <| ctx) a' (typeSubst b (TyExists alpha) b')
    (TyExists b , b') | b `notElem` freeVars b' -> instantiateL ctx b b' -- <:InstantiateL
    (b', TyExists b)  | b `notElem` freeVars b' -> instantiateR ctx b' b -- <:InstantiateR
    (a,b) -> error $ concat ["Type mismatch between '", show a, "' and '", show b, "'"]

----------------------------------------
--                                    --
--   Figure 10. Instantiation         --
--                                    --
----------------------------------------

-- Here we solve some extentials to other types. The rule InstLSolve is useful
-- for monotypes so ^a can be instantiated to a monotype easily. 

-- Γ ⊢ ^α :=< A ⊣ ∆
instantiateL :: MonadState Int m => Context -> Id -> Ty 'Poly -> m Context
instantiateL ctx a tyA =
  case toMono tyA of
    Just mono -> pure $ solve ctx a mono -- InstLSolve
    Nothing -> case tyA of -- InstLReach
        TyExists b | isAfter a b -> pure $ solve ctx b (TyExists a)
                   | otherwise   -> pure $ solve ctx a (TyExists b)
        TyFun a1 a2 -> do -- InstLArr
          alpha1 <- newName
          alpha2 <- newName
          let toAdd = [ElSolved a (TyFun (TyExists alpha1) (TyExists alpha2)), ElExists alpha1, ElExists alpha2]
          theta <- instantiateR (insertAt ctx (ElExists a) toAdd) a1 alpha1
          instantiateL theta alpha2 (applyCtx theta a2)
        TyForall b b' -> do -- InstLAllR
          alpha1 <- newName
          ctx' <- instantiateL (ElTy alpha1 <| ctx) alpha1 (typeSubst b (TyAlpha alpha1) b')
          pure $ dropCtx (ElTy alpha1) ctx'
        _ -> error "Impossible c: btw it happened on InstantiateL"
    where
      isAfter a b = isOrdered ctx (ElExists a) (ElExists b)

-- Γ ⊢ A =<: ^α ⊣ ∆ 
instantiateR :: MonadState Int m => Context -> Ty 'Poly -> Id -> m Context
instantiateR ctx tyA a =
  case toMono tyA of
    Just mono -> pure $ solve ctx a mono -- InstLSolve
    Nothing -> case tyA of -- InstLReach
        TyExists b | isAfter a b -> pure $ solve ctx b (TyExists a)
                   | otherwise   -> pure $ solve ctx a (TyExists b)
        TyFun a1 a2 -> do -- InstRArr
          alpha1 <- newName
          alpha2 <- newName
          let toAdd = [ElSolved a (TyFun (TyExists alpha1) (TyExists alpha2)), ElExists alpha1, ElExists alpha2]
          theta <- instantiateL (insertAt ctx (ElExists a) toAdd) alpha1 a1
          instantiateR theta (applyCtx theta a2) alpha2
        TyForall b b' -> do -- InstRAllL
          beta1 <- newName
          ctx' <- instantiateR (ElExists beta1 <| ElMarker beta1 <| ctx) (typeSubst b (TyAlpha beta1) b') beta1
          pure $ dropCtx (ElMarker beta1) ctx'
        _ -> error "Impossible c: btw it happened on InstantiateR"
    where
      isAfter a b = isOrdered ctx (ElExists a) (ElExists b)

----------------------------------------
--                                    --
--   Figure 11. Algorithmic typing    --
--                                    --
----------------------------------------

-- Γ ⊢ e ⇒ A ⊣ ∆
typeSynth :: MonadState Int m => Context -> Expr -> m (Context, Ty 'Poly)
typeSynth ctx = \case
  Var s -> pure (ctx, fromMaybe (error ("Cannot find variable " ++ s)) (findVar ctx s)) -- Var
  Lam s ex -> do -- Hindley milner full inference →I'
    alpha1 <- newName
    alpha2 <- newName
    let ctx' = ElVar s (TyExists alpha1) <| ElExists alpha2 <| ElExists alpha1 <| ElMarker alpha1 <|  ctx
    ctxRes <- typeCheck ctx' ex (TyExists alpha2)
    let (delta', delta) = breakOn ctxRes (ElMarker alpha1)
    let unsolvedA = getUnsolved delta'
    let t = applyCtx delta' (TyFun (TyExists alpha1) (TyExists alpha2))
    names <- replicateM (length unsolvedA) newName
    let tyInternal = typeSubsts (zip unsolvedA (map TyAlpha names)) t
    let resTy = foldr TyForall tyInternal names
    pure (delta, resTy)
  App e1 e2 -> do -- →E
    (theta, tyA) <- typeSynth ctx e1
    typeApply theta (applyCtx theta tyA) e2
  Ann ex ty -> -- Anno
    if typeWellFormed ctx ty
      then (, ty) <$> typeCheck ctx ex ty
      else error $ "Bad formed type: " ++ show ty

-- Γ ⊢ e ⇐ A ⊣ ∆
typeCheck :: MonadState Int m => Context -> Expr -> Ty 'Poly -> m Context
typeCheck ctx expr ty = case (expr, ty) of
  (e, TyForall b a) -> do -- ∀I
    alpha <- newName
    ctx' <- typeCheck (ElTy alpha <| ctx) e (typeSubst b (TyAlpha alpha) a)
    pure $ dropCtx (ElTy alpha) ctx'
  (Lam x e, TyFun a b) -> do -- →I⇒
    ctx' <- typeCheck (ElVar x a <| ctx) e a
    pure $ dropCtx (ElVar x a) ctx'
  (e, b) -> do -- Sub 
    (theta, ty') <- typeSynth ctx e
    subType theta (applyCtx theta ty') (applyCtx theta b)

-- Γ ⊢ A • e ⇒⇒ C ⊣ ∆
typeApply :: MonadState Int m => Context -> Ty 'Poly -> Expr -> m (Context, Ty 'Poly)
typeApply ctx ty expr = case (ty, expr) of
  (TyExists a, e) -> do -- extAApp
    alpha1 <- newName
    alpha2 <- newName
    let toAdd = [ElSolved a (TyFun (TyExists alpha1) (TyExists alpha2)), ElExists alpha1, ElExists alpha2]
    delta <- typeCheck (insertAt ctx (ElExists a) toAdd) expr (TyExists alpha1)
    pure (delta, TyExists alpha2)
  (TyFun a c, e) -> do -- →App
    delta <- typeCheck ctx e a
    pure (delta, c)
  (TyForall alpha a, e) -> do -- ∀App
    alpha1 <- newName
    typeApply ctx (typeSubst alpha (TyExists alpha1) a) e
  (_, _) -> error "Impossible :c"

runInference :: Expr -> Ty 'Poly 
runInference expr = let (ctx, ty) = evalState (typeSynth (Context []) expr) 1 in 
                    applyCtx ctx ty