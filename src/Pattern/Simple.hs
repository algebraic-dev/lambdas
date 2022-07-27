module Pattern.Simple where

import Data.Text                    (Text)
import Data.HashSet                 (HashSet)
import Data.List                    (nub)
import Data.List.NonEmpty           (NonEmpty(..))
import Data.HashMap.Internal.Strict (HashMap)
import GHC.Stack                    (HasCallStack)

import qualified Data.HashSet as HashSet
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Text as Text

data Pat
  = Wild
  | Cons Text [Pat]
  | Or Pat Pat
  deriving Show

showPat :: Bool -> Pat -> Text
showPat _ Wild                   = "_"
showPat _ (Cons c [])            = c
showPat False (Cons c r)         = c <> " " <> Text.intercalate " " (showPat True <$> r)
showPat False (Or a@(Cons {}) b) = showPat False a <> " | " <> showPat False b
showPat False (Or a b)           = showPat True a <> " | " <> showPat False b
showPat True  t                  = "(" <> showPat False t <> ")"

type Context = (HashMap Text (HashSet (Text, Int)), HashMap Text (Text, Int))

mkCtx :: HasCallStack => [(Text, [(Text, Int)])] -> Context
mkCtx c =
  let tys = HashSet.fromList <$> HashMap.fromList c
      cons =  HashMap.fromList $ concatMap (\(t, n) -> (\s -> (fst s, (t, snd s))) <$> n) c
  in (tys, cons)

-- Patterns

-- General detials:
-- - Matrix P is exhaustive, if and only if U (P, ( · · · )) is false.
-- - Row number i in matrix P is useless, if and only if U(P [1...i), ~p i) is false.

-- | Root constructors of the first column of the pattern stack.

getSigma :: HasCallStack => [[Pat]] -> [Text]
getSigma pats = nub $ mconcat $ fmap getRow pats where
  getRow = \case
    []         -> error "Checker Error: Should not have empty rows in get sigma"
    Wild:_     -> []
    Or p q: _  -> getRow [p] <> getRow [q]
    Cons c _:_ -> [c]

-- | Finds a type signature by the constructor name
-- Invariant: The constructor and type MUST exist (it assumes a well typed program).

findTypeSignatureByCons :: HasCallStack => Context -> Text -> HashSet (Text, Int)
findTypeSignatureByCons (signatures, constToTy) name =
  let (typeName, _) = HashMap.lookupDefault (error "Checker Error: Cannot find constructor type") name constToTy
  in HashMap.lookupDefault (error "Checker Error: Cannot find type signature") typeName signatures

findConsSize :: HasCallStack => Context -> Text -> Int
findConsSize (_, constToTy) name =
  snd $ HashMap.lookupDefault (error "Checker Error: Cannot find constructor type") name constToTy

-- | This function returns all the constructors in the type if and only if the first column
-- constitutes a complete set.
-- Invariant: All the constructors in NonEmpty Text are from the same type.

isComplete :: HasCallStack => Context -> [[Pat]] -> Maybe (HashSet (Text, Int))
isComplete ctx patStack =
  case getSigma patStack of
    [] -> error "Probably void?"
    (x : xs) ->
      let typeSig = findTypeSignatureByCons ctx x in
      if length (x : xs) == length typeSig
        then Just typeSig
        else Nothing

-- | The default matrix of Sigma in case it's not a complete signature D(P)
-- It probably removes all
defaultMatrix :: HasCallStack => [[Pat]] -> [[Pat]]
defaultMatrix = concatMap getRow where
  getRow = \case
    []          -> error "Checker Error: Should not have empty rows in default matrix"
    Cons c _:_  -> []
    Wild:rest   -> [rest]
    Or p q:rest -> defaultMatrix [p:rest, q:rest]

-- | Specializes a pattern first row in a constructor
specialize :: HasCallStack => Text -> Int -> [[Pat]] -> [[Pat]]
specialize name size = concatMap getRow where
  getRow = \case
    [] -> error "Checker Error: Should not have empty rows in specialization"
    Or p q:rest  -> specialize name size [(p:rest), (q:rest)]
    Wild : rest  -> [replicate size Wild <> rest]
    Cons c args:rest
      | c == name -> [args <> rest]
      | otherwise -> []

isUseful :: HasCallStack => Context -> [[Pat]] -> [Pat] -> Bool
isUseful _ [] _ = True
isUseful _ _ [] = False
isUseful ctx patStack q@(Cons c a : rest) = let size = findConsSize ctx c in isUseful ctx (specialize c size patStack) (a <> rest) -- Not sure if it's correct
isUseful ctx patStack   (Or p q   : rest) = isUseful ctx patStack (p : rest) ||isUseful ctx patStack (q : rest)
isUseful ctx patStack   (Wild     : rest) =
  case isComplete ctx patStack of
    Just typeSig -> or $ map (\(cons,size) -> isUseful ctx (specialize cons size patStack) (replicate size Wild ++ rest)) (HashSet.toList typeSig)
    Nothing      -> isUseful ctx (defaultMatrix patStack) rest

isExhaustive :: HasCallStack => Context -> [Pat] -> Bool
isExhaustive ctx pats = isUseful ctx ((: []) <$> pats) [Wild]