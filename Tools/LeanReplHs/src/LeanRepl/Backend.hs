-- | Lean REPL backend process management: discovery of the repl executable,
-- spawning under @lake env@, and the JSON-over-stdio request cycle.
--
-- This ports the relevant parts of LeanInteract's server module: requests are
-- one JSON document followed by a blank line; responses are read until the
-- blank-line delimiter.
module LeanRepl.Backend
  ( Backend (..)
  , BackendConfig (..)
  , discoverReplExe
  , findProject
  , isBuiltProject
  , spawnBackend
  , killBackend
  , request
  , RequestError (..)
  ) where

import Control.Exception (IOException, SomeException, try)
import Control.Monad (filterM, forM)
import Data.List (sortOn)
import Data.Maybe (catMaybes, listToMaybe)
import Data.Ord (Down (..))
import System.Directory
  ( doesDirectoryExist
  , doesFileExist
  , getCurrentDirectory
  , listDirectory
  )
import System.Environment (lookupEnv)
import System.Exit (ExitCode)
import System.FilePath ((</>), takeDirectory)
import System.IO
  ( BufferMode (..)
  , Handle
  , hClose
  , hFlush
  , hGetLine
  , hPutStr
  , hSetBuffering
  , hSetEncoding
  , hSetNewlineMode
  , universalNewlineMode
  , utf8
  )
import System.Process
  ( CreateProcess (..)
  , ProcessHandle
  , StdStream (..)
  , createProcess
  , proc
  , terminateProcess
  , waitForProcess
  )
import System.Timeout (timeout)

import LeanRepl.Json (JValue, encodeJson, parseJson)

data BackendConfig = BackendConfig
  { bcLakePath :: FilePath
  , bcReplExe :: FilePath
  , bcWorkingDir :: FilePath
  }
  deriving (Show)

data Backend = Backend
  { beIn :: Handle
  , beOut :: Handle
  , beErr :: Handle
  , beProc :: ProcessHandle
  }

data RequestError
  = ServerClosed String   -- ^ backend died; payload is captured stderr
  | RequestTimeout
  | BadResponse String
  deriving (Show)

-- Discovery -----------------------------------------------------------------

-- | Locate the repl executable built by LeanInteract (the Python sibling of
-- this tool), or honor the LEANREPL_BACKEND environment variable.
--
-- The cache layout is
--   <site-packages>/lean_interact/cache/<owner>/repl/<rev>/.lake/build/bin/repl.exe
discoverReplExe :: IO (Maybe FilePath)
discoverReplExe = do
  fromEnv <- lookupEnv "LEANREPL_BACKEND"
  case fromEnv of
    Just path -> do
      exists <- doesFileExist path
      pure (if exists then Just path else Nothing)
    Nothing -> do
      localAppData <- lookupEnv "LOCALAPPDATA"
      case localAppData of
        Nothing -> pure Nothing
        Just lad -> do
          let pythons = lad </> "Python"
          versions <- listDirIfExists pythons
          caches <- forM versions $ \v -> do
            let cache = pythons </> v </> "Lib" </> "site-packages"
                  </> "lean_interact" </> "cache"
            ok <- doesDirectoryExist cache
            pure (if ok then Just cache else Nothing)
          candidates <- concat <$> mapM replBinariesUnder (catMaybes caches)
          -- prefer newest toolchains (directory names embed the version)
          pure (listToMaybe (sortOn Down candidates))
 where
  listDirIfExists dir = do
    ok <- doesDirectoryExist dir
    if ok then listDirectory dir else pure []

  replBinariesUnder cache = do
    owners <- listSubdirs cache
    fmap concat . forM owners $ \owner -> do
      let replRoot = owner </> "repl"
      revs <- listSubdirs replRoot
      flip filterM (map binaryIn revs) doesFileExist

  binaryIn rev = rev </> ".lake" </> "build" </> "bin" </> "repl.exe"

  listSubdirs dir = do
    ok <- doesDirectoryExist dir
    if not ok
      then pure []
      else do
        entries <- listDirectory dir
        filterM doesDirectoryExist (map (dir </>) entries)

-- | Nearest enclosing Lake project that has been built, falling back to the
-- nearest project of any kind (port of the Python find_project).
findProject :: IO (Maybe FilePath)
findProject = do
  cwd <- getCurrentDirectory
  candidates <- filterM hasLakefile (ancestry cwd)
  built <- filterM isBuiltProject candidates
  pure (listToMaybe built `orElse` listToMaybe candidates)
 where
  orElse (Just x) _ = Just x
  orElse Nothing y = y

  ancestry dir =
    let parent = takeDirectory dir
    in dir : if parent == dir then [] else ancestry parent

  hasLakefile dir = do
    toml <- doesFileExist (dir </> "lakefile.toml")
    lean <- doesFileExist (dir </> "lakefile.lean")
    pure (toml || lean)

isBuiltProject :: FilePath -> IO Bool
isBuiltProject dir =
  doesDirectoryExist (dir </> ".lake" </> "build" </> "lib" </> "lean")

-- Process lifecycle ---------------------------------------------------------

spawnBackend :: BackendConfig -> IO Backend
spawnBackend config = do
  (Just hIn, Just hOut, Just hErr, ph) <- createProcess
    (proc (bcLakePath config) ["env", bcReplExe config])
      { cwd = Just (bcWorkingDir config)
      , std_in = CreatePipe
      , std_out = CreatePipe
      , std_err = CreatePipe
      }
  mapM_ prepare [hIn, hOut, hErr]
  pure (Backend hIn hOut hErr ph)
 where
  prepare h = do
    hSetEncoding h utf8
    hSetNewlineMode h universalNewlineMode
    hSetBuffering h LineBuffering

killBackend :: Backend -> IO ()
killBackend backend = do
  _ <- try (hClose (beIn backend)) :: IO (Either IOException ())
  terminateProcess (beProc backend)
  _ <- try (waitForProcess (beProc backend))
    :: IO (Either SomeException ExitCode)
  pure ()

-- Request cycle -------------------------------------------------------------

-- | Send one request and read the blank-line-delimited JSON response.
request :: Backend -> Maybe Int {-^ timeout, seconds -} -> JValue
        -> IO (Either RequestError JValue)
request backend timeoutSecs payload = do
  sendResult <- try $ do
    hPutStr (beIn backend) (encodeJson payload ++ "\n\n")
    hFlush (beIn backend)
  case (sendResult :: Either IOException ()) of
    Left _ -> Left . ServerClosed <$> drainStderr backend
    Right () -> do
      response <- withTimeout (readResponse backend)
      case response of
        Nothing -> pure (Left RequestTimeout)
        Just (Left err) -> pure (Left err)
        Just (Right text) -> case parseJson text of
          Left err -> pure (Left (BadResponse (err ++ "\nin: " ++ text)))
          Right v -> pure (Right v)
 where
  withTimeout action = case timeoutSecs of
    Nothing -> Just <$> action
    Just secs -> timeout (secs * 1000000) action

readResponse :: Backend -> IO (Either RequestError String)
readResponse backend = go []
 where
  go acc = do
    line <- try (hGetLine (beOut backend))
    case (line :: Either IOException String) of
      Left _ -> Left . ServerClosed <$> drainStderr backend
      Right l
        | null l && not (null acc) -> pure (Right (unlines (reverse acc)))
        | null l -> go acc  -- leading blank line; keep waiting
        | otherwise -> go (l : acc)

drainStderr :: Backend -> IO String
drainStderr backend = go [] (200 :: Int)
 where
  go acc 0 = done acc
  go acc n = do
    line <- try (timeout 200000 (hGetLine (beErr backend)))
    case (line :: Either IOException (Maybe String)) of
      Right (Just l) -> go (l : acc) (n - 1)
      _ -> done acc
  done acc = pure (unlines (reverse acc))
