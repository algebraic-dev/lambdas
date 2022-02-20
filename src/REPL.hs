module REPL where

-- It's useful for testing and using each type system interactively
-- You can use some unicodes inside of it.

import Data.Text (Text)
import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.State (MonadState)

import qualified Data.Text           as Text
import qualified Data.Text.IO        as TextIO
import qualified System.IO           as IO
import qualified Control.Monad.State as State
import qualified System.Console.ANSI as ANSI

data ReplState =
  MkReplState { replHistory       :: [Text]
              , replBuffer        :: Text
              , replPosition      :: Int
              , replHistoricPos   :: Int
              , replOnUnicodeMode :: Bool
              , replUnicodeBuffer :: Text
              }

newtype REPL a = MkREPL { getREPLState :: State.StateT ReplState IO a}
  deriving (Functor, Applicative, Monad, MonadState ReplState, MonadIO)

-- Helper functions

startState :: ReplState
startState = MkReplState [] "" 0 (-1) False ""

safeEmpty :: Text -> (Text -> Text) -> Text
safeEmpty ""   action = ""
safeEmpty text action = action text

splitOn :: ReplState -> (Text, Text)
splitOn state = Text.splitAt (replPosition state) (replBuffer state)

bounds :: Int -> Int -> Int -> Int
bounds min' max' cur = min max' (max min' cur)

-- Operations to manipulate the ReplState

getKey :: MonadIO m => m Text
getKey = Text.pack . reverse <$> liftIO (getKey' "")
  where getKey' chars = do
          char <- getChar
          more <- IO.hReady IO.stdin
          (if more then getKey' else return) (char:chars)

initRaw :: MonadIO m => m ()
initRaw = liftIO $ do
  IO.hSetBuffering IO.stdin IO.NoBuffering
  IO.hSetEcho IO.stdin False

resetUnicode :: REPL ()
resetUnicode = State.modify (\s -> s { replOnUnicodeMode = False, replUnicodeBuffer = "" })

setBuffer :: Text -> REPL ()
setBuffer text = State.modify (\s -> s { replBuffer = text })

setPos :: Int -> REPL ()
setPos pos = State.modify (\s -> s { replPosition = pos })

modifyUBuffer :: (Text -> Text) -> REPL ()
modifyUBuffer action = do
  let res state = action (replUnicodeBuffer state)
  State.modify (\s -> s { replUnicodeBuffer = res s, replOnUnicodeMode = res s /= "" })

addPos :: Int -> REPL ()
addPos add = do
  current <- State.gets replPosition
  len <- State.gets (Text.length . replBuffer)
  setPos (bounds 0 (max len 0) (current+add))

resetBuffer :: REPL ()
resetBuffer = setBuffer "" *> setPos 0

setTextBuffer :: Text -> REPL ()
setTextBuffer text = setBuffer text >> setPos (Text.length text)

addToBuffer :: Text -> REPL ()
addToBuffer text = do
  onUnicodeMode <- State.gets replOnUnicodeMode
  if onUnicodeMode
    then modifyUBuffer (<> text)
    else do
      (left, right) <- State.gets splitOn
      setBuffer (left <> text <> right)
      addPos 1

remFromBuffer :: REPL ()
remFromBuffer = do
  onUnicodeMode <- State.gets replOnUnicodeMode
  if onUnicodeMode
    then modifyUBuffer (`safeEmpty` Text.init)
    else do
      (left, right) <- State.gets splitOn
      setBuffer (safeEmpty left Text.init <> right)
      addPos (-1)

historicMove :: Int -> REPL ()
historicMove amount = do
  (idx, history, buffer) <- State.gets (\s -> (replHistoricPos s, replHistory s, replBuffer s))
  let newPos = bounds (-1) (length history - 1) (idx + amount)
  State.modify (\s -> s { replHistoricPos = newPos })
  setTextBuffer $ if | newPos < 0              -> ""
                     | newPos < length history -> history !! newPos
                     | otherwise               -> buffer

breakLine :: (Text -> IO ()) -> REPL ()
breakLine action = do
  buffer <- State.gets replBuffer
  liftIO $ putStr "\n" >> action buffer >> putStr "\n"
  State.modify (\s -> s { replHistory = buffer : replHistory s, replHistoricPos = -1})
  setTextBuffer ""

-- Cool IO functions 

prompt :: MonadIO m => Text -> m ()
prompt text = liftIO $ do
  TextIO.putStr text
  IO.hFlush IO.stdout

putText :: MonadIO m => Text -> m ()
putText = liftIO . TextIO.putStr

-- Repl manipulation

repl :: (Text -> IO ()) -> IO ()
repl action = do
  initRaw
  prompt "> "
  State.evalStateT (getREPLState $ loop action) startState

keyLoop :: (Text -> IO ()) -> Text -> REPL ()
keyLoop action = \case
    "\\"     -> State.modify (\s -> s { replOnUnicodeMode = True, replUnicodeBuffer = "\\" })
    "\ESC[A" -> resetUnicode >> historicMove 1
    "\ESC[B" -> resetUnicode >> historicMove (-1)
    "\ESC[C" -> resetUnicode >> addPos 1
    "\ESC[D" -> resetUnicode >> addPos (-1)
    "\n"     -> resetUnicode >> breakLine action
    "\f"     -> liftIO $ ANSI.clearScreen >> ANSI.setCursorPosition 0 0
    "\DEL"   -> remFromBuffer
    key      -> if Text.length key == 1
                  then addToBuffer key
                  else pure ()

matchStr :: Text -> Maybe Text 
matchStr = \case 
  "\\lambda" -> Just "λ"
  "\\mul"    -> Just "×"
  "\\forall" -> Just "∀"
  _        -> Nothing

matchBuffer :: REPL ()
matchBuffer = do 
  buffer <- State.gets replUnicodeBuffer
  case matchStr buffer of 
    Nothing -> pure ()
    Just txt -> resetUnicode >> addToBuffer txt
    

renderREPL :: REPL ()
renderREPL = do
    matchBuffer
    state <- State.get
    let (left, right) = splitOn state
    liftIO $ do
      ANSI.clearLine
      ANSI.setCursorColumn 0
      TextIO.putStr "> "
      TextIO.putStr left
      ANSI.setSGR [ ANSI.SetColor ANSI.Foreground ANSI.Vivid ANSI.Red]
      TextIO.putStr (replUnicodeBuffer state)
      ANSI.setSGR [ ANSI.Reset ]
      TextIO.putStr right
      ANSI.setCursorColumn (replPosition state + Text.length (replUnicodeBuffer state) + 2)
      IO.hFlush IO.stdout

loop :: (Text -> IO ()) -> REPL ()
loop action = do
  key <- getKey
  when (key /= "\ESC") $ do
    keyLoop action key
    renderREPL
    loop action