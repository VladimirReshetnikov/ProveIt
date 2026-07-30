{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}

-- | leanrepl-hs - a GHCi-style interactive REPL for Lean 4.
--
-- Haskell port of Tools/LeanRepl/leanrepl.py. The Haskeline loop follows the
-- structure of the Djex REPL driver (interrupt-safe step function, logical
-- multi-line input, command completion).
module Main (main) where

import Control.Exception (SomeException, try)
import Control.Monad (forM_, unless, when)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.IORef
import Data.List (intercalate, isPrefixOf, isSuffixOf, nub)
import Data.Maybe (fromMaybe, isJust)
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.Time.Format (defaultTimeLocale, formatTime)
import Data.Time.LocalTime (getZonedTime)
import System.Console.Haskeline
import System.Directory
  ( doesDirectoryExist
  , doesFileExist
  , getHomeDirectory
  , listDirectory
  )
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath ((</>), (<.>), takeDirectory, takeFileName)
import System.IO
import System.IO.Error (catchIOError, isEOFError)
import System.Process (callCommand)

import LeanRepl.Backend
import LeanRepl.Builtins (builtinInfo)
import LeanRepl.Classify
import LeanRepl.Format (formatInfo, indentDefBody)
import LeanRepl.Json

#ifdef mingw32_HOST_OS
import Data.Bits ((.|.))
import Data.Word (Word32)
import Foreign.Marshal.Alloc (alloca)
import Foreign.Ptr (Ptr)
import Foreign.Storable (peek)
import Foreign.C.Types (CInt (..))

foreign import ccall unsafe "GetStdHandle"
  c_GetStdHandle :: Word32 -> IO (Ptr ())
foreign import ccall unsafe "GetConsoleMode"
  c_GetConsoleMode :: Ptr () -> Ptr Word32 -> IO CInt
foreign import ccall unsafe "SetConsoleMode"
  c_SetConsoleMode :: Ptr () -> Word32 -> IO CInt

-- Enable virtual-terminal processing so ANSI escapes render in the classic
-- Windows console. Returns False if the console refuses.
enableVT :: IO Bool
enableVT = do
  result <- try $ do
    handle <- c_GetStdHandle 0xFFFFFFF5  -- STD_OUTPUT_HANDLE (-11)
    alloca $ \modePtr -> do
      ok <- c_GetConsoleMode handle modePtr
      if ok == 0
        then pure False
        else do
          mode <- peek modePtr
          ok' <- c_SetConsoleMode handle (mode .|. 0x0004)
          pure (ok' /= 0)
  pure (either (\e -> const False (e :: SomeException)) id result)
#else
enableVT :: IO Bool
enableVT = pure True
#endif

-- State ---------------------------------------------------------------------

data ReplState = ReplState
  { rsBackend :: Maybe Backend
  , rsConfig :: BackendConfig
  , rsProjectDir :: Maybe FilePath
  , rsEnv :: Maybe Integer
  , rsBaseEnv :: Maybe Integer
  , rsEnvStack :: [Maybe Integer]
  , rsImports :: [String]
  , rsHistory :: [String]
  , rsLoadedFile :: Maybe FilePath
  , rsShowTime :: Bool
  , rsTimestamps :: Bool
  , rsTranscript :: Maybe (FilePath, Handle)
  , rsTimeout :: Maybe Int
  , rsColor :: Bool
  , rsInteractive :: Bool
    -- ^ False when stdin is piped: prompts and echo go through emit (so the
    -- output and transcript read like a session) and Haskeline's own
    -- locale-encoded prompt printing is bypassed.
  }

type St = IORef ReplState

-- Output (all user-visible text flows through emit so transcripts capture
-- the whole session) --------------------------------------------------------

emit :: St -> String -> IO ()
emit st text = do
  state <- readIORef st
  putStr text
  hFlush stdout
  forM_ (rsTranscript state) $ \(_, h) -> do
    hPutStr h (stripAnsi text)
    hFlush h

emitLn :: St -> String -> IO ()
emitLn st text = emit st (text ++ "\n")

stripAnsi :: String -> String
stripAnsi [] = []
stripAnsi ('\27' : '[' : rest) = stripAnsi (drop 1 (dropWhile (/= 'm') rest))
stripAnsi (c : rest) = c : stripAnsi rest

color :: St -> String -> String -> IO String
color st code text = do
  state <- readIORef st
  pure (if rsColor state then "\27[" ++ code ++ "m" ++ text ++ "\27[0m" else text)

cRed, cYellow, cCyan, cDim, cBold :: St -> String -> IO String
cRed st = color st "31"
cYellow st = color st "33"
cCyan st = color st "36"
cDim st = color st "2"
cBold st = color st "1"

-- Transcript ----------------------------------------------------------------

transcriptStart :: St -> Maybe FilePath -> IO ()
transcriptStart st mpath = do
  state <- readIORef st
  case rsTranscript state of
    Just (p, _) -> emitLn st =<< cDim st ("already recording to " ++ p)
    Nothing -> do
      path <- case mpath of
        Just p -> pure p
        Nothing -> do
          now <- getZonedTime
          pure (formatTime defaultTimeLocale "leanrepl-%Y%m%d-%H%M%S.log" now)
      result <- try (openFile path AppendMode)
      case (result :: Either SomeException Handle) of
        Left err -> emitLn st =<< cRed st ("cannot open transcript file: " ++ show err)
        Right h -> do
          hSetEncoding h utf8
          now <- getZonedTime
          hPutStrLn h ("-- LeanRepl transcript started "
            ++ formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S" now)
          hFlush h
          modifyIORef' st (\s -> s { rsTranscript = Just (path, h) })
          stamps <- rsTimestamps <$> readIORef st
          emitLn st =<< cDim st ("recording transcript to " ++ path
            ++ (if stamps then " (with per-command timestamps)" else ""))

transcriptStop :: St -> IO ()
transcriptStop st = do
  state <- readIORef st
  case rsTranscript state of
    Nothing -> emitLn st =<< cDim st "transcript is not active"
    Just (path, h) -> do
      now <- getZonedTime
      hPutStrLn h ("-- LeanRepl transcript ended "
        ++ formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S" now)
      hClose h
      modifyIORef' st (\s -> s { rsTranscript = Nothing })
      emitLn st =<< cDim st ("transcript saved to " ++ path)

-- Record an input line (with its prompt) in the transcript; Haskeline's echo
-- does not pass through emit.
transcriptInput :: St -> String -> String -> IO ()
transcriptInput st promptText line = do
  state <- readIORef st
  forM_ (rsTranscript state) $ \(_, h) -> do
    when (rsTimestamps state && promptText == mainPrompt) $ do
      now <- getZonedTime
      hPutStrLn h (formatTime defaultTimeLocale "[%H:%M:%S]" now)
    hPutStrLn h (promptText ++ line)
    hFlush h

mainPrompt, contPrompt :: String
mainPrompt = "\955> "
contPrompt = "\8230> "

-- Backend interaction -------------------------------------------------------

-- Ensure a live backend, respawning and replaying the session after a crash
-- or interrupt (port of AutoLeanServer's restart-and-replay behavior).
ensureBackend :: St -> IO (Either String Backend)
ensureBackend st = do
  state <- readIORef st
  case rsBackend state of
    Just backend -> pure (Right backend)
    Nothing -> do
      emitLn st =<< cDim st "starting Lean backend..."
      result <- try (spawnBackend (rsConfig state))
      case (result :: Either SomeException Backend) of
        Left err -> pure (Left (show err))
        Right backend -> do
          modifyIORef' st (\s -> s { rsBackend = Just backend })
          rebuilt <- rebuildSession st
          if rebuilt then pure (Right backend)
            else pure (Left "failed to rebuild the session")

backendDied :: St -> IO ()
backendDied st = do
  state <- readIORef st
  forM_ (rsBackend state) killBackend
  modifyIORef' st (\s -> s { rsBackend = Nothing })

-- Run a command in an environment. Nothing env = fresh (imports allowed).
runCmd :: St -> Maybe Integer -> String -> IO (Either String JValue)
runCmd st env code = do
  backendOr <- ensureBackend st
  case backendOr of
    Left err -> pure (Left err)
    Right backend -> do
      state <- readIORef st
      let payload = JObj (("cmd", JStr code)
            : [("env", JInt e) | Just e <- [env]])
      result <- request backend (rsTimeout state) payload
      case result of
        Right v -> pure (Right v)
        Left RequestTimeout -> do
          backendDied st
          pure (Left ("timeout after "
            ++ maybe "?" show (rsTimeout state)
            ++ "s - the backend was killed; the session replays on the next command"))
        Left (ServerClosed stderrText) -> do
          backendDied st
          pure (Left ("the Lean server died"
            ++ (if null (trim stderrText) then "" else ":\n" ++ stderrText)
            ++ "\nhint: check that the project is built (lake build) and that "
            ++ "enough memory is available; the session replays on the next command"))
        Left (BadResponse err) -> pure (Left ("bad response: " ++ err))

-- Response accessors --------------------------------------------------------

respEnv :: JValue -> Maybe Integer
respEnv v = jLookup "env" v >>= jInt

respMessages :: JValue -> [(String, String)]  -- (severity, data)
respMessages v = fromMaybe [] $ do
  msgs <- jLookup "messages" v >>= jArray
  pure [ (sev, dat)
       | m <- msgs
       , Just sev <- [jLookup "severity" m >>= jString]
       , Just dat <- [jLookup "data" m >>= jString]
       ]

respSorries :: JValue -> [(Maybe Integer, String)]  -- (proofState, goal)
respSorries v = fromMaybe [] $ do
  sorries <- jLookup "sorries" v >>= jArray
  pure [ (jLookup "proofState" s >>= jInt, goal)
       | s <- sorries
       , Just goal <- [jLookup "goal" s >>= jString]
       ]

respFatal :: JValue -> Maybe String
respFatal v = case jLookup "message" v of
  Just (JStr m) | not (isJust (jLookup "env" v)) -> Just m
  _ -> Nothing

hasErrors :: JValue -> Bool
hasErrors v = any ((== "error") . fst) (respMessages v)

looksIncomplete :: JValue -> Bool
looksIncomplete v =
  let errs = [d | (s, d) <- respMessages v, s == "error"]
  in not (null errs) && all ("unexpected end of input" `isInfixOf'`) errs
 where
  isInfixOf' needle hay = any (needle `isPrefixOf`) (suffixes hay)
  suffixes s = s : case s of
    _ : rest -> suffixes rest
    [] -> []

-- Print messages/sorries; returns True if there were errors.
printResponse :: St -> Maybe (String -> Maybe String) -> JValue -> IO Bool
printResponse st transform v = case respFatal v of
  Just m -> do
    emitLn st . (++ m) =<< cRed st "REPL error: "
    pure True
  Nothing -> do
    errored <- newIORef False
    forM_ (respMessages v) $ \(severity, rawText) -> do
      let text = trimEnd (applyTransform severity rawText)
      case severity of
        "error" -> do
          writeIORef errored True
          emitLn st . (++ text) =<< cRed st "error: "
        "warning" ->
          unless ("declaration uses" `isPrefixOf` text) $
            emitLn st . (++ text) =<< cYellow st "warning: "
        _ -> emitLn st text
    forM_ (respSorries v) $ \(proofState, goal) -> do
      tag <- cCyan st "sorry"
      note <- cDim st (" (proof state " ++ maybe "?" show proofState ++ ")")
      emitLn st (tag ++ note)
      forM_ (lines (trimEnd goal)) $ \l -> emitLn st ("  " ++ l)
    readIORef errored
 where
  applyTransform "info" text = fromMaybe text (transform >>= \f -> f text)
  applyTransform _ text = text
  trimEnd = reverse . dropWhile isSpace . reverse

-- Session (re)construction --------------------------------------------------

-- Build the base environment from imports and replay history (used on
-- startup after a crash, and when imports change).
rebuildSession :: St -> IO Bool
rebuildSession st = do
  state <- readIORef st
  baseOk <- case rsImports state of
    [] -> do
      modifyIORef' st (\s -> s { rsBaseEnv = Nothing })
      pure True
    imports -> do
      emitLn st =<< cDim st ("importing: " ++ intercalate ", " imports ++ " ...")
      warnMissingModules st imports
      started <- getCurrentTime
      result <- runCmd st Nothing (unlines (map ("import " ++) imports))
      case result of
        Left err -> do
          emitLn st . (++ err) =<< cRed st "import failed: "
          pure False
        Right v -> do
          errored <- printResponse st Nothing v
          if errored then pure False else do
            -- a failed import yields a silently *empty* environment; probe
            probe <- runCmd st (respEnv v) "example : True := True.intro"
            case probe of
              Right pv | not (hasErrors pv) -> do
                modifyIORef' st (\s -> s { rsBaseEnv = respEnv v })
                finished <- getCurrentTime
                emitLn st =<< cDim st ("imports ready in "
                  ++ show (round (diffUTCTime finished started) :: Integer) ++ "s")
                pure True
              _ -> do
                emitLn st =<< cRed st
                  "import failed: the resulting environment is unusable"
                pure False
  if not baseOk then pure False else do
    stateNow <- readIORef st
    modifyIORef' st (\s -> s { rsEnv = rsBaseEnv stateNow, rsEnvStack = [] })
    replay (rsHistory stateNow) []
 where
  replay [] done = do
    modifyIORef' st (\s -> s { rsHistory = reverse done })
    pure True
  replay (code : rest) done = do
    env <- rsEnv <$> readIORef st
    result <- runCmd st env code
    case result of
      Right v | not (hasErrors v) -> do
        modifyIORef' st (\s -> s { rsEnv = respEnv v })
        replay rest (code : done)
      _ -> do
        emitLn st =<< cRed st ("replay failed at: "
          ++ takeWhile (/= '\n') code)
        modifyIORef' st (\s -> s { rsHistory = reverse done })
        pure False

-- Module availability (the backend silently ignores unresolvable imports).
moduleAvailable :: St -> String -> IO Bool
moduleAvailable st modName = do
  state <- readIORef st
  let root = takeWhile (/= '.') modName
  if root `elem` ["Init", "Std", "Lean"] then pure True else
    case rsProjectDir state of
      Nothing -> pure False
      Just project -> do
        let relative = foldr1 (</>) (splitOn '.' modName) <.> "olean"
            buildLib dir = dir </> ".lake" </> "build" </> "lib" </> "lean"
            packagesDir = project </> ".lake" </> "packages"
        packageDirs <- do
          ok <- doesDirectoryExist packagesDir
          if not ok then pure [] else
            map (packagesDir </>) <$> listDirectory packagesDir
        let roots = buildLib project : map buildLib packageDirs
        results <- mapM (\r -> doesFileExist (r </> relative)) roots
        pure (or results)

warnMissingModules :: St -> [String] -> IO ()
warnMissingModules st mods = forM_ mods $ \m -> do
  ok <- moduleAvailable st m
  unless ok $ do
    state <- readIORef st
    let hint = case rsProjectDir state of
          Just p -> "run `lake build` in " ++ p
          Nothing -> "plain mode has no project modules"
    warning <- cYellow st "warning: "
    emitLn st (warning ++ "module " ++ m
      ++ " not found in the build tree - the backend will silently ignore it ("
      ++ hint ++ ")")

splitOn :: Char -> String -> [String]
splitOn sep s = case break (== sep) s of
  (chunk, []) -> [chunk]
  (chunk, _ : rest) -> chunk : splitOn sep rest

-- Evaluation ----------------------------------------------------------------

data EvalOutcome = EvalDone | EvalIncomplete

advanceEnv :: St -> Maybe Integer -> String -> IO ()
advanceEnv st newEnv code = modifyIORef' st $ \s -> s
  { rsEnvStack = rsEnv s : rsEnvStack s
  , rsEnv = newEnv
  , rsHistory = rsHistory s ++ [code]
  }

evalInput :: St -> Bool -> String -> IO EvalOutcome
evalInput st allowIncomplete rawText = do
  let text = trim rawText
  if null text then pure EvalDone else do
    started <- getCurrentTime
    outcome <-
      if firstToken text == "import"
        then do
          let mods = [ trim (drop 7 (trim l))
                     | l <- lines text, "import " `isPrefixOf` trim l ]
          cmdImport st mods
          pure EvalDone
        else if isDeclaration text
          then do
            env <- rsEnv <$> readIORef st
            result <- runCmd st env text
            case result of
              Left err -> do
                emitLn st =<< cRed st err
                pure EvalDone
              Right v
                | allowIncomplete && looksIncomplete v -> pure EvalIncomplete
                | otherwise -> do
                    errored <- printResponse st Nothing v
                    unless errored (advanceEnv st (respEnv v) text)
                    pure EvalDone
          else do
            evalExpression st text
            pure EvalDone
    showTimeFlag <- rsShowTime <$> readIORef st
    when showTimeFlag $ do
      finished <- getCurrentTime
      emitLn st =<< cDim st ("(" ++ show (diffUTCTime finished started) ++ ")")
    pure outcome

-- GHCi-style: try #eval, fall back to #check, then raw, then built-in help.
evalExpression :: St -> String -> IO ()
evalExpression st text = do
  env <- rsEnv <$> readIORef st
  evalResult <- runCmd st env ("#eval (" ++ text ++ ")")
  case evalResult of
    Right v | not (hasErrors v), Nothing <- respFatal v ->
      () <$ printResponse st Nothing v
    Left err -> emitLn st =<< cRed st err
    _ -> do
      checkResult <- runCmd st env ("#check (" ++ text ++ ")")
      case checkResult of
        Right v | not (hasErrors v), Nothing <- respFatal v ->
          () <$ printResponse st Nothing v
        _ -> do
          rawResult <- runCmd st env text
          case rawResult of
            Right v | not (hasErrors v), Nothing <- respFatal v -> do
              _ <- printResponse st Nothing v
              advanceEnv st (respEnv v) text
            _ -> do
              printed <- printBuiltinInfo st text
              unless printed $ case evalResult of
                Right v -> () <$ printResponse st Nothing v
                Left err -> emitLn st =<< cRed st err

printBuiltinInfo :: St -> String -> IO Bool
printBuiltinInfo st token = case builtinInfo token of
  Nothing -> pure False
  Just text -> do
    emitLn st =<< cCyan st ("built-in: " ++ trim token)
    forM_ (lines text) $ \l -> emitLn st ("  " ++ l)
    pure True

-- Commands ------------------------------------------------------------------

helpText :: String
helpText = unlines
  [ ""
  , "Enter Lean declarations (def, theorem, ...) or expressions (evaluated with"
  , "#eval, falling back to #check). Multi-line input starts when a line is"
  , "syntactically incomplete; an empty line submits it. :{ and :} delimit an"
  , "explicit block."
  , ""
  , "Commands (GHCi-style):"
  , "  :help, :h, :?            show this help"
  , "  :quit, :q                exit the REPL"
  , "  :type EXPR, :t EXPR      show the type of EXPR       (#check)"
  , "  :info NAME, :i NAME      show the definition of NAME (#print)"
  , "  :load FILE, :l FILE      reset the session and load a .lean file"
  , "  :reload, :r              reload the last loaded file"
  , "  :import MOD              add an import (rebuilds the session)"
  , "  :imports                 list active imports"
  , "  :set OPT VAL             set_option OPT VAL (persists in the session)"
  , "  :undo                    revert the last state-changing command"
  , "  :reset                   clear all definitions (keeps imports)"
  , "  :history                 show state-changing commands of this session"
  , "  :env                     show the current environment id"
  , "  :time                    toggle per-command timing"
  , "  :transcript [FILE|on|off] record a full transcript of the session"
  , "  :timestamps [on|off]     timestamp each command in the transcript"
  , "  :pickle FILE             save the current environment to FILE (.olean)"
  , "  :unpickle FILE           restore an environment from FILE"
  , "  :! CMD                   run a shell command"
  , "Any #-prefixed Lean command (#eval, #check, #print axioms) works directly."
  ]

commandNames :: [String]
commandNames =
  [ ":help", ":quit", ":type", ":info", ":load", ":reload", ":import"
  , ":imports", ":set", ":undo", ":reset", ":history", ":env", ":time"
  , ":transcript", ":timestamps", ":pickle", ":unpickle"
  ]

-- Returns False when the REPL should exit.
dispatchCommand :: St -> String -> IO Bool
dispatchCommand st line = do
  let (word, rest) = break isSpace (drop 1 (trim line))
      arg = trim rest
  case word of
    w | w `elem` ["q", "quit", "exit"] -> pure False
    w | w `elem` ["h", "help", "?"] -> True <$ emit st helpText
    w | w `elem` ["t", "type"] -> True <$ cmdType st arg
    w | w `elem` ["i", "info"] -> True <$ cmdInfo st arg
    w | w `elem` ["l", "load"] -> True <$ cmdLoad st arg
    w | w `elem` ["r", "reload"] -> do
      loaded <- rsLoadedFile <$> readIORef st
      case loaded of
        Just path -> cmdLoad st path
        Nothing -> emitLn st =<< cRed st "no file has been loaded"
      pure True
    "import" -> True <$ cmdImport st (words (map decomma arg))
    "imports" -> do
      imports <- rsImports <$> readIORef st
      if null imports
        then emitLn st =<< cDim st "(no imports)"
        else forM_ imports (\m -> emitLn st ("import " ++ m))
      pure True
    "set" -> do
      if null arg
        then emitLn st =<< cRed st "usage: :set OPTION VALUE"
        else do
          env <- rsEnv <$> readIORef st
          result <- runCmd st env ("set_option " ++ arg)
          case result of
            Left err -> emitLn st =<< cRed st err
            Right v -> do
              errored <- printResponse st Nothing v
              unless errored (advanceEnv st (respEnv v) ("set_option " ++ arg))
      pure True
    "undo" -> do
      state <- readIORef st
      case rsEnvStack state of
        [] -> emitLn st =<< cRed st "nothing to undo"
        prev : stack -> do
          let (dropped, history) = case reverse (rsHistory state) of
                h : hs -> (Just h, reverse hs)
                [] -> (Nothing, [])
          writeIORef st state
            { rsEnv = prev, rsEnvStack = stack, rsHistory = history }
          forM_ dropped $ \d ->
            emitLn st =<< cDim st ("undid: " ++ takeWhile (/= '\n') d)
      pure True
    "reset" -> do
      modifyIORef' st $ \s -> s
        { rsHistory = [], rsEnvStack = [], rsEnv = rsBaseEnv s }
      imports <- rsImports <$> readIORef st
      emitLn st =<< cDim st
        ("session reset" ++ if null imports then "" else " (imports kept)")
      pure True
    "history" -> do
      history <- rsHistory <$> readIORef st
      if null history
        then emitLn st =<< cDim st "(empty)"
        else forM_ (zip [1 :: Int ..] history) $ \(i, h) ->
          emitLn st (pad i ++ "  " ++ takeWhile (/= '\n') h
            ++ (if '\n' `elem` h then " \8230" else ""))
      pure True
    "env" -> do
      env <- rsEnv <$> readIORef st
      emitLn st ("environment id: " ++ maybe "(none)" show env)
      pure True
    "time" -> do
      modifyIORef' st (\s -> s { rsShowTime = not (rsShowTime s) })
      enabled <- rsShowTime <$> readIORef st
      emitLn st =<< cDim st ("timing " ++ if enabled then "on" else "off")
      pure True
    "transcript" -> do
      case arg of
        "" -> do
          state <- readIORef st
          case rsTranscript state of
            Just (p, _) -> emitLn st ("recording to " ++ p
              ++ if rsTimestamps state then " (with timestamps)" else "")
            Nothing -> emitLn st =<< cDim st
              "transcript is off  (:transcript on|FILE to start)"
        "off" -> transcriptStop st
        "on" -> transcriptStart st Nothing
        path -> transcriptStart st (Just path)
      pure True
    "timestamps" -> do
      case arg of
        a | a `elem` ["on", "true", "1", "yes"] ->
          modifyIORef' st (\s -> s { rsTimestamps = True })
        a | a `elem` ["off", "false", "0", "no"] ->
          modifyIORef' st (\s -> s { rsTimestamps = False })
        "" -> modifyIORef' st (\s -> s { rsTimestamps = not (rsTimestamps s) })
        _ -> emitLn st =<< cRed st "usage: :timestamps [on|off]"
      enabled <- rsTimestamps <$> readIORef st
      emitLn st =<< cDim st
        ("per-command timestamps " ++ if enabled then "on" else "off")
      pure True
    "pickle" -> True <$ cmdPickle st arg
    "unpickle" -> True <$ cmdUnpickle st arg
    "!" -> do
      result <- try (callCommand arg)
      case (result :: Either SomeException ()) of
        Left err -> emitLn st =<< cRed st (show err)
        Right () -> pure ()
      pure True
    _ -> do
      emitLn st =<< cRed st ("unknown command :" ++ word ++ "  (:help for help)")
      pure True
 where
  decomma c = if c == ',' then ' ' else c
  pad i = let s = show i in replicate (3 - length s) ' ' ++ s

cmdType :: St -> String -> IO ()
cmdType st arg
  | null arg = emitLn st =<< cRed st "usage: :type EXPR"
  | otherwise = do
      env <- rsEnv <$> readIORef st
      result <- runCmd st env ("#check (" ++ arg ++ ")")
      case result of
        Left err -> emitLn st =<< cRed st err
        Right v
          | hasErrors v || isJust (respFatal v) -> do
              printed <- printBuiltinInfo st arg
              unless printed (() <$ printResponse st Nothing v)
          | otherwise -> () <$ printResponse st Nothing v

cmdInfo :: St -> String -> IO ()
cmdInfo st arg
  | null arg = emitLn st =<< cRed st "usage: :info NAME"
  | otherwise = do
      env <- rsEnv <$> readIORef st
      printResult <- runCmd st env ("#print " ++ arg)
      case printResult of
        Left err -> emitLn st =<< cRed st err
        Right v
          | hasErrors v || isJust (respFatal v) -> do
              checkResult <- runCmd st env ("#check (" ++ arg ++ ")")
              case checkResult of
                Right cv | not (hasErrors cv), Nothing <- respFatal cv ->
                  () <$ printResponse st Nothing cv
                _ -> do
                  printed <- printBuiltinInfo st arg
                  unless printed (() <$ printResponse st Nothing v)
          | otherwise -> () <$ printResponse st
              (Just (\t -> formatInfo t `orElse` indentDefBody t)) v
 where
  orElse (Just x) _ = Just x
  orElse Nothing y = y

cmdImport :: St -> [String] -> IO ()
cmdImport st mods
  | null mods = emitLn st =<< cRed st "usage: :import MODULE"
  | otherwise = do
      state <- readIORef st
      fresh <- newModules st (rsImports state) mods
      if null fresh
        then emitLn st =<< cDim st "no new modules to import"
        else do
          let oldImports = rsImports state
          modifyIORef' st (\s -> s { rsImports = oldImports ++ fresh })
          emitLn st =<< cDim st
            "rebuilding session with new imports (this re-elaborates history)..."
          ok <- rebuildSession st
          unless ok $ do
            modifyIORef' st (\s -> s { rsImports = oldImports })
            emitLn st =<< cRed st "import failed; session unchanged"
            _ <- rebuildSession st
            pure ()

newModules :: St -> [String] -> [String] -> IO [String]
newModules st existing mods = go (nub mods) []
 where
  go [] acc = pure (reverse acc)
  go (m : rest) acc
    | m `elem` existing = go rest acc
    | otherwise = do
        ok <- moduleAvailable st m
        if ok then go rest (m : acc) else do
          warnMissingModules st [m]
          go rest acc

cmdLoad :: St -> String -> IO ()
cmdLoad st arg
  | null arg = emitLn st =<< cRed st "usage: :load FILE"
  | otherwise = do
      let path0 = arg
      exists0 <- doesFileExist path0
      let path = if exists0 || '.' `elem` takeFileName path0
            then path0 else path0 <.> "lean"
      exists <- doesFileExist path
      if not exists
        then emitLn st =<< cRed st ("file not found: " ++ path)
        else do
          contents <- readFileUtf8 path
          let (fileImports, body) = splitHeader contents
          -- GHCi-style :load resets the session to the file contents
          modifyIORef' st $ \s -> s { rsHistory = [], rsEnvStack = [] }
          state <- readIORef st
          fresh <- newModules st (rsImports state) fileImports
          modifyIORef' st (\s -> s { rsImports = rsImports s ++ fresh })
          emitLn st =<< cDim st ("loading " ++ path ++ " ...")
          started <- getCurrentTime
          ok <- rebuildSession st
          if not ok
            then emitLn st =<< cRed st "failed to elaborate imports"
            else do
              bodyOk <- if null (trim body) then pure True else do
                baseEnv <- rsBaseEnv <$> readIORef st
                result <- runCmd st baseEnv body
                case result of
                  Left err -> False <$ (emitLn st =<< cRed st err)
                  Right v -> do
                    errored <- printResponse st Nothing v
                    modifyIORef' st (\s -> s { rsEnv = respEnv v })
                    unless errored $ modifyIORef' st
                      (\s -> s { rsHistory = [body] })
                    pure True
              when bodyOk $ do
                modifyIORef' st (\s -> s { rsLoadedFile = Just path })
                finished <- getCurrentTime
                emitLn st =<< cDim st ("loaded " ++ takeFileName path
                  ++ " (" ++ show (length (lines body)) ++ " lines) in "
                  ++ show (round (diffUTCTime finished started) :: Integer) ++ "s")
 where
  splitHeader contents = go (lines contents) []
   where
    go [] imports = (reverse imports, "")
    go (l : rest) imports
      | "import " `isPrefixOf` trim l =
          go rest (trim (drop 7 (trim l)) : imports)
      | null (trim l) || "--" `isPrefixOf` trim l = go rest imports
      | otherwise = (reverse imports, intercalate "\n" (l : rest))

cmdPickle :: St -> String -> IO ()
cmdPickle st arg
  | null arg = emitLn st =<< cRed st "usage: :pickle FILE"
  | otherwise = do
      backendOr <- ensureBackend st
      case backendOr of
        Left err -> emitLn st =<< cRed st err
        Right backend -> do
          state <- readIORef st
          let path = withOlean arg
              payload = JObj
                [ ("pickleTo", JStr path)
                , ("env", JInt (fromMaybe 0 (rsEnv state)))
                ]
          result <- request backend (rsTimeout state) payload
          case result of
            Right v -> do
              errored <- printResponse st Nothing v
              unless errored $
                emitLn st =<< cDim st ("environment saved to " ++ path)
            Left err -> emitLn st =<< cRed st (show err)

cmdUnpickle :: St -> String -> IO ()
cmdUnpickle st arg
  | null arg = emitLn st =<< cRed st "usage: :unpickle FILE"
  | otherwise = do
      backendOr <- ensureBackend st
      case backendOr of
        Left err -> emitLn st =<< cRed st err
        Right backend -> do
          state <- readIORef st
          let path = withOlean arg
              payload = JObj [("unpickleEnvFrom", JStr path)]
          result <- request backend (rsTimeout state) payload
          case result of
            Right v -> do
              errored <- printResponse st Nothing v
              unless errored $ do
                modifyIORef' st $ \s -> s
                  { rsEnvStack = rsEnv s : rsEnvStack s
                  , rsEnv = respEnv v
                  }
                emitLn st =<< cDim st ("environment restored from " ++ path)
            Left err -> emitLn st =<< cRed st (show err)

withOlean :: String -> String
withOlean path =
  if ".olean" `isSuffixOf` path then path else path ++ ".olean"

readFileUtf8 :: FilePath -> IO String
readFileUtf8 path = do
  h <- openFile path ReadMode
  hSetEncoding h utf8
  contents <- hGetContents h
  length contents `seq` hClose h
  pure contents

-- Main loop -----------------------------------------------------------------

banner :: String
banner = unlines
  [ ""
  , "  __                          ___"
  , " / /  ___ ___ ____  ______ __/ _ \\___ ___  / /"
  , "/ /__/ -_) _ `/ _ \\/ __/ // / , _/ -_) _ \\/ /"
  , "\\____|__/\\_,_/_//_/_/  \\_, /_/|_|\\___/ .__/_/"
  , "                      /___/         /_/"
  ]

replLoop :: St -> InputT IO ()
replLoop st = do
  step <- handleInterrupt onInterrupt $ withInterrupt $ do
    input <- readLogicalInput st
    case input of
      Nothing -> do
        liftIO (emitLn st =<< cDim st "goodbye")
        pure False
      Just text
        | null (trim text) -> pure True
        | ":" `isPrefixOf` trim text && not (":=" `isPrefixOf` trim text) ->
            liftIO (dispatchCommand st (trim text))
        | otherwise -> do
            evalWithRetry text
            pure True
  when step (replLoop st)
 where
  onInterrupt = do
    liftIO $ do
      emitLn st =<< cRed st "interrupted"
      state <- readIORef st
      when (isJust (rsBackend state)) $ do
        backendDied st
        emitLn st =<< cDim st
          "the Lean backend was restarted; the session replays on the next command"
    pure True

  evalWithRetry text = do
    outcome <- liftIO (evalInput st True text)
    case outcome of
      EvalDone -> pure ()
      EvalIncomplete -> do
        extra <- readContinuationLines st []
        if null extra
          then () <$ liftIO (evalInput st False text)
          else evalWithRetry (text ++ "\n" ++ intercalate "\n" extra)

-- Read one line, handling prompt display, echo, and transcript capture for
-- both interactive and piped stdin.
readLine :: St -> String -> InputT IO (Maybe String)
readLine st promptText = do
  interactive <- liftIO (rsInteractive <$> readIORef st)
  if interactive
    then do
      input <- getInputLine promptText
      forM_ input (liftIO . transcriptInput st promptText)
      pure input
    else do
      liftIO $ do
        state <- readIORef st
        when (rsTimestamps state && promptText == mainPrompt) $
          forM_ (rsTranscript state) $ \(_, h) -> do
            now <- getZonedTime
            hPutStrLn h (formatTime defaultTimeLocale "[%H:%M:%S]" now)
        emit st promptText
      -- read stdin directly: Haskeline's file backend decodes with the
      -- locale codepage, corrupting UTF-8 input on Windows
      input <- liftIO (catchIOError (Just <$> getLine)
        (\e -> if isEOFError e then pure Nothing else ioError e))
      case input of
        Nothing -> Nothing <$ liftIO (emitLn st "")
        Just l -> do
          liftIO (emitLn st l)  -- echo piped input so transcripts are readable
          pure (Just l)

readContinuationLines :: St -> [String] -> InputT IO [String]
readContinuationLines st acc = do
  next <- readLine st contPrompt
  case next of
    Nothing -> pure (reverse acc)
    Just l
      | null (trim l) -> pure (reverse acc)
      | otherwise -> readContinuationLines st (l : acc)

-- One logical (possibly multi-line) input; Nothing on EOF.
readLogicalInput :: St -> InputT IO (Maybe String)
readLogicalInput st = do
  input <- readLine st mainPrompt
  case input of
    Nothing -> pure Nothing
    Just line -> case () of
      _ | trim line == ":{" -> Just <$> collectBlock []
        | ":" `isPrefixOf` trim line && not (":=" `isPrefixOf` trim line) ->
            pure (Just line)
        | needsContinuation line -> do
            extra <- readContinuationLines st []
            pure (Just (intercalate "\n" (line : extra)))
        | otherwise -> pure (Just line)
 where
  collectBlock acc = do
    next <- readLine st contPrompt
    case next of
      Nothing -> pure (intercalate "\n" (reverse acc))
      Just l
        | trim l == ":}" -> pure (intercalate "\n" (reverse acc))
        | otherwise -> collectBlock (l : acc)

completionSettings :: Settings IO
completionSettings = Settings
  { complete = completeWord Nothing " \t" completer
  , historyFile = Nothing  -- set in main
  , autoAddHistory = True
  }
 where
  completer word
    | ":" `isPrefixOf` word =
        pure [simpleCompletion c | c <- commandNames, word `isPrefixOf` c]
    | otherwise = pure []

-- CLI -----------------------------------------------------------------------

data Options = Options
  { optProject :: Maybe FilePath
  , optPlain :: Bool
  , optImports :: [String]
  , optTimeout :: Int
  , optTime :: Bool
  , optTranscript :: Maybe (Maybe FilePath)
  , optTimestamps :: Bool
  , optReplExe :: Maybe FilePath
  , optLake :: FilePath
  , optFile :: Maybe FilePath
  }

defaultOptions :: Options
defaultOptions = Options Nothing False [] 300 False Nothing False Nothing "lake" Nothing

parseArgs :: [String] -> Either String Options
parseArgs = go defaultOptions
 where
  go opts [] = Right opts
  go opts (a : rest) = case a of
    "--project" -> withValue rest (\v r -> go opts { optProject = Just v } r)
    "-p" -> withValue rest (\v r -> go opts { optProject = Just v } r)
    "--plain" -> go opts { optPlain = True } rest
    "--import" -> withValue rest (\v r ->
      go opts { optImports = optImports opts ++ splitCommas v } r)
    "-i" -> withValue rest (\v r ->
      go opts { optImports = optImports opts ++ splitCommas v } r)
    "--timeout" -> withValue rest (\v r -> case reads v of
      [(n, "")] -> go opts { optTimeout = n } r
      _ -> Left "--timeout expects a number")
    "--time" -> go opts { optTime = True } rest
    "--transcript" -> case rest of
      v : r | not ("-" `isPrefixOf` v) ->
        go opts { optTranscript = Just (Just v) } r
      _ -> go opts { optTranscript = Just Nothing } rest
    "--timestamps" -> go opts { optTimestamps = True } rest
    "--repl-exe" -> withValue rest (\v r -> go opts { optReplExe = Just v } r)
    "--lake" -> withValue rest (\v r -> go opts { optLake = v } r)
    "--help" -> Left usage
    _ | "-" `isPrefixOf` a -> Left ("unknown option " ++ a ++ "\n" ++ usage)
      | otherwise -> go opts { optFile = Just a } rest

  withValue (v : rest) k = k v rest
  withValue [] _ = Left "missing option value"

  splitCommas = filter (not . null) . splitOn ','

usage :: String
usage = unlines
  [ "usage: leanrepl-hs [FILE] [options]"
  , "  --project DIR    path to a Lake project to run inside"
  , "  --plain          do not use any Lake project (backend project only)"
  , "  -i, --import M   module to import at startup (repeatable)"
  , "  --timeout N      per-command timeout in seconds (0 = none, default 300)"
  , "  --time           show per-command timing"
  , "  --transcript [F] record a full transcript of the session"
  , "  --timestamps     timestamp each command in the transcript"
  , "  --repl-exe PATH  Lean REPL backend executable (see also LEANREPL_BACKEND)"
  , "  --lake PATH      lake executable (default: lake)"
  ]

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

main :: IO ()
main = do
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  hSetBuffering stdout (BlockBuffering Nothing)
  args <- getArgs
  case parseArgs args of
    Left message -> putStrLn message >> exitWith (ExitFailure 2)
    Right opts -> run opts

run :: Options -> IO ()
run opts = do
  vtOk <- enableVT
  tty <- hIsTerminalDevice stdout
  interactive <- hIsTerminalDevice stdin
  let useColor = vtOk && tty

  replExe <- case optReplExe opts of
    Just path -> pure (Just path)
    Nothing -> discoverReplExe
  case replExe of
    Nothing -> do
      putStrLn "error: could not find the Lean REPL backend executable."
      putStrLn "Build it once via the Python sibling (Tools/LeanRepl), or pass"
      putStrLn "--repl-exe / set LEANREPL_BACKEND to a repl.exe built from"
      putStrLn "https://github.com/leanprover-community/repl for your toolchain."
      exitWith (ExitFailure 1)
    Just exe -> do
      project <- case (optPlain opts, optProject opts) of
        (True, _) -> pure Nothing
        (_, Just dir) -> pure (Just dir)
        _ -> findProject
      -- plain mode runs in the backend's own Lake project
      let backendProject = takeDirectory (takeDirectory
            (takeDirectory (takeDirectory (takeDirectory exe))))
          workingDir = fromMaybe backendProject project
          config = BackendConfig
            { bcLakePath = optLake opts
            , bcReplExe = exe
            , bcWorkingDir = workingDir
            }
      st <- newIORef ReplState
        { rsBackend = Nothing
        , rsConfig = config
        , rsProjectDir = project
        , rsEnv = Nothing
        , rsBaseEnv = Nothing
        , rsEnvStack = []
        , rsImports = optImports opts
        , rsHistory = []
        , rsLoadedFile = Nothing
        , rsShowTime = optTime opts
        , rsTimestamps = optTimestamps opts
        , rsTranscript = Nothing
        , rsTimeout = if optTimeout opts <= 0 then Nothing
            else Just (optTimeout opts)
        , rsColor = useColor
        , rsInteractive = interactive
        }

      forM_ (optTranscript opts) (transcriptStart st)
      case project of
        Just dir -> do
          emitLn st =<< cDim st ("using Lake project: " ++ dir)
          built <- isBuiltProject dir
          unless built $ do
            warning <- cYellow st "warning: "
            emitLn st (warning ++ dir ++ " has no .lake build - run `lake build` there first")
        Nothing -> emitLn st =<< cDim st
          ("no Lake project; using the backend's own project (" ++ backendProject ++ ")")

      -- startup probe (spawns the backend and surfaces setup problems early)
      started <- getCurrentTime
      probe <- runCmd st Nothing "#eval (0 : Nat)"
      case probe of
        Left err -> do
          emitLn st =<< cRed st "the Lean backend failed to start:"
          emitLn st err
          exitWith (ExitFailure 1)
        Right _ -> do
          finished <- getCurrentTime
          emitLn st =<< cDim st ("backend responding ("
            ++ show (round (diffUTCTime finished started) :: Integer) ++ "s)")

      -- imports requested on the command line
      importsOk <- do
        imports <- rsImports <$> readIORef st
        if null imports then pure True else rebuildSession st
      unless importsOk $ emitLn st =<< cRed st "startup imports failed"

      emit st =<< cCyan st banner
      bold1 <- cBold st ":help"
      bold2 <- cBold st ":quit"
      emitLn st ("LeanRepl (Haskell) - a GHCi-style REPL for Lean 4.  Type "
        ++ bold1 ++ " for help, " ++ bold2 ++ " to exit.")

      forM_ (optFile opts) (cmdLoad st)

      home <- getHomeDirectory
      let settings = completionSettings
            { historyFile = if interactive
                then Just (home </> ".leanrepl_history")
                else Nothing }
          behavior = if interactive then defaultBehavior else useFileHandle stdin
      runInputTBehavior behavior settings (replLoop st)

      -- cleanup
      state <- readIORef st
      when (isJust (rsTranscript state)) (transcriptStop st)
      forM_ (rsBackend state) killBackend
