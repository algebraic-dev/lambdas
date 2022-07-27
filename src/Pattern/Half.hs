module Pattern.Half where

import Control.Applicative          (asum)
import Data.Text                    (Text)
import Data.HashSet                 (HashSet)
import Data.List                    (nub)
import Data.List.NonEmpty           (NonEmpty(..))
import Data.HashMap.Internal.Strict (HashMap)
import GHC.Stack                    (HasCallStack)
import Pattern.Simple               hiding (isUseful, isComplete)

import qualified Data.HashSet        as HashSet
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Text           as Text

useful :: Context -> [Pat] -> Maybe [Pat]
useful ctx pats = isUseful ctx ((: []) <$> pats) 1

isComplete :: HasCallStack => Context -> [Text] -> Maybe (HashSet (Text, Int))
isComplete ctx sigma =
  case sigma of
    [] -> Nothing
    (x : xs) ->
      let typeSig = findTypeSignatureByCons ctx x in
      if length (x : xs) == length typeSig
        then Just typeSig
        else Nothing

isUseful :: Context -> [[Pat]] -> Int -> Maybe [Pat]
isUseful _ [] _ = Just []
isUseful _ _  0 = Nothing
isUseful ctx env n =
  let sigma = getSigma env in
  case isComplete ctx sigma of
    Just typeSig -> do
      ((c, s), result) <- asum $ fmap (\i@(name, size) -> (i, ) <$> isUseful ctx (specialize name size env) (size + n - 1)) (HashSet.toList typeSig)
      let pats = take s result
      let res  = drop s result
      pure (Cons c pats : res)
    Nothing      -> do
      result <- isUseful ctx (defaultMatrix env) (n - 1)
      case sigma of
        [] -> Just (Wild : result)
        (x: xs) ->
          let allCons    = findTypeSignatureByCons ctx x
              sigmaSet   = HashSet.fromList sigma
              res        = HashSet.toList $ HashSet.filter (\(n, _) -> not $ HashSet.member n sigmaSet) allCons
              (x' : xs') = fmap (\(c,s) -> Cons c (replicate s Wild)) res
          in pure (foldr Or x' xs' : result)