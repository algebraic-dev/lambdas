module Main where
import REPL
import qualified Data.Text as Text
import System.IO

import qualified Type.Utils.Parser as Parser
import qualified Text.Megaparsec   as Mp
import qualified Type.Dunfield     as Dunfield

main :: IO ()
main = repl $ \text -> do
  case Mp.runParser Parser.parseDunfieldExpr "REPL" text of
    Left err   -> putStrLn $ "\n" ++ Mp.errorBundlePretty err
    Right expr -> either putStrLn print (Dunfield.runInference expr)