{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}

-- | leant - a GHCi-style interactive REPL for Lean 4.
--
-- Haskell port of Tools/LeantPy/leant.py. The Haskeline loop follows the
-- structure of the Djex REPL driver (interrupt-safe step function, logical
-- multi-line input, command completion).
module Main (main) where

import Control.Exception (SomeException, finally, try)
import Control.Monad (forM_, unless, when)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isAlphaNum, isSpace, toLower)
import Data.IORef
import Data.List (intercalate, isInfixOf, isPrefixOf, isSuffixOf, nub, stripPrefix)
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

import Leant.Backend
import Leant.Builtins (builtinInfo)
import Leant.Classify
import Leant.Format (formatInfo, indentDefBody)
import Leant.Json

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

foreign import ccall unsafe "GetConsoleOutputCP"
  c_GetConsoleOutputCP :: IO Word32
foreign import ccall unsafe "SetConsoleOutputCP"
  c_SetConsoleOutputCP :: Word32 -> IO CInt
foreign import ccall unsafe "GetConsoleCP"
  c_GetConsoleCP :: IO Word32
foreign import ccall unsafe "SetConsoleCP"
  c_SetConsoleCP :: Word32 -> IO CInt

-- The console renders our UTF-8 output bytes in its OEM codepage (CP437:
-- \945 shows as ╬▒) unless the output codepage is UTF-8. Switch both
-- codepages to 65001 and return an action restoring the originals.
setupConsoleUtf8 :: IO (IO ())
setupConsoleUtf8 = do
  result <- try $ do
    oldOut <- c_GetConsoleOutputCP
    oldIn <- c_GetConsoleCP
    _ <- c_SetConsoleOutputCP 65001
    _ <- c_SetConsoleCP 65001
    pure $ do
      _ <- c_SetConsoleOutputCP oldOut
      _ <- c_SetConsoleCP oldIn
      pure ()
  pure (either (\e -> const (pure ()) (e :: SomeException)) id result)

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
setupConsoleUtf8 :: IO (IO ())
setupConsoleUtf8 = pure (pure ())

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
  , rsProve :: Maybe ProveState
  , rsProveCounter :: Int
  , rsLastSorry :: Maybe (Integer, String)
  , rsItCounter :: Int
    -- ^ GHCi-style `it`: evaluations bind `def \171it!N\187 := (expr)`; bare
    -- `it` in later input is substituted with the newest binding
  , rsComplCache :: [(String, [String])]
  , rsBrowseEnv :: Maybe Integer
    -- ^ cached environment for :browse - session imports plus
    -- Lean.Elab.Command (so the introspection metaprogram elaborates without
    -- polluting the user's own environment); invalidated on import changes
  , rsTimeout :: Maybe Int
  , rsColor :: Bool
  , rsInteractive :: Bool
    -- ^ False when stdin is piped: prompts and echo go through emit (so the
    -- output and transcript read like a session) and Haskeline's own
    -- locale-encoded prompt printing is bypassed.
  }

-- | Interactive prove mode: the stack holds (proofState, goals, scriptEntry)
-- newest first; the entry state has no script entry.
data ProveState = ProveState
  { pvStmt :: Maybe String  -- ^ Nothing when resumed from a `sorry`
  , pvStack :: [(Integer, [String], Maybe String)]
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
          pure (formatTime defaultTimeLocale "leant-%Y%m%d-%H%M%S.log" now)
      result <- try (openFile path AppendMode)
      case (result :: Either SomeException Handle) of
        Left err -> emitLn st =<< cRed st ("cannot open transcript file: " ++ show err)
        Right h -> do
          hSetEncoding h utf8
          now <- getZonedTime
          hPutStrLn h ("-- Leant transcript started "
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
      hPutStrLn h ("-- Leant transcript ended "
        ++ formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S" now)
      hClose h
      modifyIORef' st (\s -> s { rsTranscript = Nothing })
      emitLn st =<< cDim st ("transcript saved to " ++ path)

-- Record an input line (with its prompt) in the transcript; Haskeline's echo
-- does not pass through emit.
transcriptInput' :: St -> Bool -> String -> String -> IO ()
transcriptInput' st isMain promptText line = do
  state <- readIORef st
  forM_ (rsTranscript state) $ \(_, h) -> do
    when (rsTimestamps state && isMain) $ do
      now <- getZonedTime
      hPutStrLn h (formatTime defaultTimeLocale "[%H:%M:%S]" now)
    hPutStrLn h (promptText ++ line)
    hFlush h

mainPrompt, contPrompt :: String
mainPrompt = "\955> "
contPrompt = "\8230> "

promptOf :: St -> IO String
promptOf st = do
  state <- readIORef st
  pure $ case rsProve state of
    Just pv -> case pvStack pv of
      (_, goals, _) : _ | length goals > 1 ->
        "\8866" ++ show (length goals) ++ "> "
      _ -> "\8866> "
    Nothing -> mainPrompt

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
runCmd st env code = runPayload st $ JObj
  (("cmd", JStr code) : [("env", JInt e) | Just e <- [env]])

-- Apply one tactic to a proof state.
runTactic :: St -> Integer -> String -> IO (Either String JValue)
runTactic st proofState tactic = runPayload st $ JObj
  [("tactic", JStr tactic), ("proofState", JInt proofState)]

runPayload :: St -> JValue -> IO (Either String JValue)
runPayload st payload = do
  backendOr <- ensureBackend st
  case backendOr of
    Left err -> pure (Left err)
    Right backend -> do
      state <- readIORef st
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
      let text = trimEnd (applyTransform severity (rewriteIt rawText))
      case severity of
        "error" -> do
          writeIORef errored True
          emitLn st . (++ text) =<< cRed st "error: "
        "warning" ->
          unless ("declaration uses" `isPrefixOf` text) $
            emitLn st . (++ text) =<< cYellow st "warning: "
        _ -> emitLn st text
    forM_ (respSorries v) $ \(proofState, goal) -> do
      forM_ proofState $ \ps -> modifyIORef' st
        (\s -> s { rsLastSorry = Just (ps, goal) })
      tag <- cCyan st "sorry"
      note <- cDim st (" (proof state " ++ maybe "?" show proofState
        ++ " \8212 :prove to work on it)")
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
  modifyIORef' st (\s -> s { rsBrowseEnv = Nothing, rsComplCache = [] })
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

-- GHCi-style `it` ------------------------------------------------------------

itName :: Int -> String
itName n = "\171it!" ++ show n ++ "\187"

-- Replace bare `it` (outside strings and comments, at identifier
-- boundaries) with the mangled name of the newest bound result.
substIt :: Int -> String -> String
substIt 0 text = text
substIt counter text = go Nothing text
 where
  target = itName counter
  go _ [] = []
  go _ ('"' : rest) =
    let (lit, rest') = takeStringLit rest in '"' : lit ++ go (Just '"') rest'
  go _ ('-' : '-' : rest) =
    let (c, r) = break (== '\n') rest in "--" ++ c ++ go (Just ' ') r
  go _ ('/' : '-' : rest) =
    let (c, r) = takeBlockComment (1 :: Int) rest
    in "/-" ++ c ++ go (Just ' ') r
  go prev ('i' : 't' : rest)
    | boundaryBefore prev, boundaryAfter rest =
        target ++ go (Just '\187') rest
  go _ (c : rest) = c : go (Just c) rest

  boundaryBefore Nothing = True
  boundaryBefore (Just c) = not (isIdentChar c) && c /= '.'
  boundaryAfter [] = True
  boundaryAfter (c : _) = not (isIdentChar c)  -- '.' allowed: it.succ
  isIdentChar c = isAlphaNum c || c `elem` "_'!?\171\187"

  takeStringLit ('\\' : c : rest) =
    let (a, b) = takeStringLit rest in ('\\' : c : a, b)
  takeStringLit ('"' : rest) = ("\"", rest)
  takeStringLit (c : rest) = let (a, b) = takeStringLit rest in (c : a, b)
  takeStringLit [] = ("", "")

  takeBlockComment _ [] = ("", "")
  takeBlockComment depth ('/' : '-' : rest) =
    let (a, b) = takeBlockComment (depth + 1) rest in ("/-" ++ a, b)
  takeBlockComment depth ('-' : '/' : rest)
    | depth <= 1 = ("-/", rest)
    | otherwise = let (a, b) = takeBlockComment (depth - 1) rest
                  in ("-/" ++ a, b)
  takeBlockComment depth (c : rest) =
    let (a, b) = takeBlockComment depth rest in (c : a, b)

-- Cosmetic: mangled it-names in backend output display as plain `it`.
rewriteIt :: String -> String
rewriteIt [] = []
rewriteIt s@(c : rest) = case stripItName s of
  Just remainder -> "it" ++ rewriteIt remainder
  Nothing -> c : rewriteIt rest
 where
  stripItName input = do
    afterMark <- stripPrefix "\171it!" input `orElse'`
      (stripPrefix "it!" input >>= ensureBare)
    let (digits, rest') = span (`elem` "0123456789") afterMark
    if null digits then Nothing else
      pure (fromMaybe rest' (stripPrefix "\187" rest'))
  -- for the guillemet-less spelling, digits must follow directly
  ensureBare r@(d : _) | d `elem` "0123456789" = Just r
  ensureBare _ = Nothing
  orElse' (Just x) _ = Just x
  orElse' Nothing y = y

bindIt :: St -> String -> IO ()
bindIt st expr = do
  state <- readIORef st
  let n = rsItCounter state + 1
      code = "def " ++ itName n ++ " := (" ++ expr ++ ")"
  result <- runCmd st (rsEnv state) code
  case result of
    Right v | not (hasErrors v), Nothing <- respFatal v -> do
      modifyIORef' st (\s -> s { rsItCounter = n })
      advanceEnv st (respEnv v) code
    _ -> pure ()

advanceEnv :: St -> Maybe Integer -> String -> IO ()
advanceEnv st newEnv code = modifyIORef' st $ \s -> s
  { rsEnvStack = rsEnv s : rsEnvStack s
  , rsEnv = newEnv
  , rsHistory = rsHistory s ++ [code]
  }

evalInput :: St -> Bool -> String -> IO EvalOutcome
evalInput st allowIncomplete rawText = do
  counter <- rsItCounter <$> readIORef st
  let text = substIt counter (trim rawText)
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
    Right v | not (hasErrors v), Nothing <- respFatal v -> do
      _ <- printResponse st Nothing v
      bindIt st text
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
  , "  :browse [NAMESPACE]      list declarations in a namespace or the session"
  , "  :browse! NAMESPACE       ...including compiler-generated auxiliaries"
  , "  :prove [PROP]            interactively prove PROP tactic by tactic"
  , "                           (no argument: resume the last `sorry`)"
  , "  :doc NAME                show the documentation string of NAME"
  , "  :search TEXT             search declaration names (case-insensitive)"
  , "  :search? TYPE            proof search: what proves TYPE? (via exact?)"
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
  , ":imports", ":browse", ":browse!", ":doc", ":prove", ":search", ":search?"
  , ":set", ":undo", ":reset", ":history", ":env", ":time", ":transcript"
  , ":timestamps", ":pickle", ":unpickle"
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
    "browse" -> True <$ cmdBrowse st False arg
    "browse!" -> True <$ cmdBrowse st True arg
    "prove" -> True <$ cmdProve st arg
    "doc" -> True <$ cmdDoc st arg
    "search" -> True <$ cmdSearch st False arg
    "search?" -> True <$ cmdSearch st True arg
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
      history <- filter (not . ("def \171it!" `isPrefixOf`)) . rsHistory
        <$> readIORef st
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
cmdType st rawArg
  | null rawArg = emitLn st =<< cRed st "usage: :type EXPR"
  | otherwise = do
      state <- readIORef st
      let arg = substIt (rsItCounter state) rawArg
          env = rsEnv state
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

-- :browse -------------------------------------------------------------------

-- The introspection metaprogram run inside the browse environment. One
-- logInfo with all matches keeps the response to a single message.
-- The namespace is spliced as string literals (not a backquoted name
-- literal), so arbitrary component spellings cannot break the parser.
browseProgram :: Bool -> [String] -> String
browseProgram showAll nameComponents = unlines $
  [ "open Lean in run_cmd do"
  , "  let env \8592 getEnv"
  , "  let pre : Name := ["
      ++ intercalate ", " (map leanStringLit nameComponents)
      ++ "].foldl (fun a s => Name.str a s) Name.anonymous"
  ]
  ++ (if showAll then
  [ "  let keep (n : Name) : Bool := !n.isInternal" ]
  else
  [ "  let aux : List String :="
  , "    [\"rec\", \"recOn\", \"casesOn\", \"brecOn\", \"binductionOn\","
  , "     \"below\", \"ibelow\", \"noConfusion\", \"noConfusionType\","
  , "     \"ctorElim\", \"ctorElimType\", \"ctorIdx\", \"sizeOf_spec\","
  , "     \"injEq\", \"inj\", \"eq_def\", \"decEq\"]"
  , "  let keep (n : Name) : Bool :="
  , "    !n.isInternalDetail &&"
  , "    !n.components.any fun c => match c with"
  , "      | .str _ s => aux.contains s"
  , "      | _ => false"
  ])
  ++
  [ "  let names := env.constants.fold (init := #[]) fun a n _ =>"
  , "    if pre.isPrefixOf n && keep n then a.push n else a"
  , "  if names.isEmpty then"
  , "    logInfo \"(no declarations found)\""
  , "  else"
  , "    let sorted := names.qsort (\183.toString < \183.toString)"
  , "    logInfo (String.intercalate \"\\n\" (sorted.toList.map toString))"
  ]

-- Build (or reuse) an environment containing the session's imports plus the
-- Lean metaprogramming API, without touching the user's environment.
ensureBrowseEnv :: St -> IO (Either String Integer)
ensureBrowseEnv = ensureBrowseEnv' False

ensureBrowseEnv' :: Bool -> St -> IO (Either String Integer)
ensureBrowseEnv' quiet st = do
  state <- readIORef st
  case rsBrowseEnv state of
    Just env -> pure (Right env)
    Nothing -> do
      unless quiet $
        emitLn st =<< cDim st "preparing browse environment (session imports + Lean)..."
      let imports = nub (rsImports state ++ ["Lean.Elab.Command"])
      result <- runCmd st Nothing (unlines (map ("import " ++) imports))
      case result of
        Left err -> pure (Left err)
        Right v
          | hasErrors v || isJust (respFatal v) -> do
              _ <- printResponse st Nothing v
              pure (Left "failed to build the browse environment")
          | otherwise -> case respEnv v of
              Nothing -> pure (Left "browse environment has no id")
              Just env -> do
                modifyIORef' st (\s -> s { rsBrowseEnv = Just env })
                pure (Right env)

leanStringLit :: String -> String
leanStringLit s = '"' : concatMap escape s ++ "\""
 where
  escape '"' = "\\\""
  escape '\\' = "\\\\"
  escape c = [c]

-- shared filter for compiler-generated auxiliary names
generatedFilterLines :: [String]
generatedFilterLines =
  [ "  let aux : List String :="
  , "    [\"rec\", \"recOn\", \"casesOn\", \"brecOn\", \"binductionOn\","
  , "     \"below\", \"ibelow\", \"noConfusion\", \"noConfusionType\","
  , "     \"ctorElim\", \"ctorElimType\", \"ctorIdx\", \"sizeOf_spec\","
  , "     \"injEq\", \"inj\", \"eq_def\", \"decEq\"]"
  , "  let keep (n : Name) : Bool :="
  , "    !n.isInternalDetail &&"
  , "    !n.components.any fun c => match c with"
  , "      | .str _ s => aux.contains s"
  , "      | _ => false"
  ]

validDottedName :: String -> Maybe [String]
validDottedName arg =
  let comps = splitOn '.' arg
  in if any isSpace arg || any null comps then Nothing else Just comps

cmdDoc :: St -> String -> IO ()
cmdDoc st rawArg = do
  let arg = dropWhile (== '@') (trim rawArg)
  case (arg, validDottedName arg) of
    ("", _) -> emitLn st =<< cRed st "usage: :doc NAME"
    (_, Nothing) -> emitLn st =<< cRed st ("invalid name `" ++ arg ++ "`")
    (_, Just comps) -> do
      envOr <- ensureBrowseEnv st
      case envOr of
        Left err -> emitLn st =<< cRed st err
        Right env -> do
          let program = unlines
                [ "open Lean in run_cmd do"
                , "  let env \8592 getEnv"
                , "  let n : Name := ["
                    ++ intercalate ", " (map leanStringLit comps)
                    ++ "].foldl (fun a s => Name.str a s) Name.anonymous"
                , "  if !env.contains n then"
                , "    logInfo s!\"unknown constant `{n}` "
                    ++ "(session-local names have no docstrings)\""
                , "  else"
                , "    match \8592 findDocString? env n with"
                , "    | some doc => logInfo doc"
                , "    | none => logInfo \"(no documentation string)\""
                ]
          result <- runCmd st (Just env) program
          case result of
            Left err -> emitLn st =<< cRed st err
            Right v -> () <$ printResponse st Nothing v

cmdSearch :: St -> Bool -> String -> IO ()
cmdSearch st byType arg
  | null arg = emitLn st =<< cRed st "usage: :search TEXT  |  :search? TYPE"
  | byType = do
      env <- rsEnv <$> readIORef st
      result <- runCmd st env ("example : (" ++ arg ++ ") := by exact?")
      case result of
        Left err -> emitLn st =<< cRed st err
        Right v
          | any (\(s, d) -> s == "error" && "unknown tactic" `isInfixOf` d)
              (respMessages v) -> do
            message <- cRed st ":search? needs the `exact?` tactic \8212 "
            hint <- cBold st ":import Mathlib.Tactic"
            emitLn st (message ++ "try " ++ hint)
          | otherwise -> () <$ printResponse st Nothing v
  | otherwise = do
      envOr <- ensureBrowseEnv st
      case envOr of
        Left err -> emitLn st =<< cRed st err
        Right env -> do
          state <- readIORef st
          -- hide Lean-API hits unless the user imported Lean themselves
          let leanImported = any (\i -> i == "Lean" || "Lean." `isPrefixOf` i)
                (rsImports state)
              hidden = if leanImported then "[]" else "[\"Lean\"]"
              program = unlines $
                [ "open Lean in run_cmd do"
                , "  let env \8592 getEnv"
                , "  let needle := (" ++ leanStringLit arg ++ ").toLower"
                , "  let hidden : List String := " ++ hidden
                ] ++ generatedFilterLines ++
                [ "  let hits := env.constants.fold (init := #[]) fun a n _ =>"
                , "    if keep n && !hidden.contains n.getRoot.toString"
                , "        && (n.toString.toLower.splitOn needle).length > 1"
                , "    then a.push n else a"
                , "  if hits.isEmpty then"
                , "    logInfo \"(no matches)\""
                , "  else"
                , "    let sorted := hits.qsort (\183.toString < \183.toString)"
                , "    let shown := sorted.toList.take 100"
                , "    let more := if sorted.size > 100 then"
                , "      s!\"\\n... ({sorted.size} matches, first 100 shown)\" else \"\""
                , "    logInfo (String.intercalate \"\\n\" (shown.map toString) ++ more)"
                ]
          result <- runCmd st (Just env) program
          case result of
            Left err -> emitLn st =<< cRed st err
            Right v -> () <$ printResponse st Nothing v
          history <- rsHistory <$> readIORef st
          let matching = [ n | n <- concatMap sessionDeclNames history
                         , lower arg `isInfixOf` lower n ]
          unless (null matching) $ do
            emitLn st =<< cDim st "-- declared in this session:"
            mapM_ (emitLn st) matching
 where
  lower = map toLower

completionCandidates :: St -> String -> IO [String]
completionCandidates st prefix = do
  state <- readIORef st
  case lookup prefix (rsComplCache state) of
    Just cached -> pure cached
    Nothing -> do
      let sessionNames =
            [ n | n <- concatMap sessionDeclNames (rsHistory state)
            , prefix `isPrefixOf` n ]
      envOr <- ensureBrowseEnv' True st
      backendNames <- case envOr of
        Left _ -> pure []
        Right env -> do
          let program = unlines $
                [ "open Lean in run_cmd do"
                , "  let env \8592 getEnv"
                , "  let pre := " ++ leanStringLit prefix
                ] ++ generatedFilterLines ++
                [ "  let hits := env.constants.fold (init := #[]) fun a n _ =>"
                , "    if keep n && pre.isPrefixOf n.toString then a.push n else a"
                , "  let sorted := hits.qsort (\183.toString < \183.toString)"
                , "  logInfo (String.intercalate \"\\n\""
                , "    (sorted.toList.take 200 |>.map toString))"
                ]
          result <- try (runCmd st (Just env) program)
          case result of
            Right (Right v) -> pure
              [ n | (sev, d) <- respMessages v, sev == "info"
              , n <- lines d, not (null n) ]
            Right (Left _) -> pure []
            Left e -> const (pure []) (e :: SomeException)
      let merged = nub (sessionNames ++ backendNames)
      modifyIORef' st (\s -> s
        { rsComplCache = (prefix, merged) : rsComplCache s })
      pure merged

cmdBrowse :: St -> Bool -> String -> IO ()
cmdBrowse st showAll rawArg
  | null arg = do
      history <- rsHistory <$> readIORef st
      let decls = concatMap sessionDeclNames history
      if null decls
        then emitLn st =<< cDim st "(no session declarations)"
        else mapM_ (emitLn st) decls
  | any isSpace arg || any null nameComponents = do
      message <- cRed st ("invalid namespace `" ++ arg ++ "`")
      emitLn st (message
        ++ " - :browse expects a dotted name such as Nat or List.Perm")
  | otherwise = do
      envOr <- ensureBrowseEnv st
      case envOr of
        Left err -> emitLn st =<< cRed st err
        Right env -> do
          result <- runCmd st (Just env)
            (browseProgram showAll nameComponents)
          case result of
            Left err -> emitLn st =<< cRed st err
            Right v -> () <$ printResponse st Nothing v
      -- the browse environment predates session declarations; list those
      -- separately from the recorded history
      history <- rsHistory <$> readIORef st
      let matching =
            [ name
            | name <- concatMap sessionDeclNames history
            , (arg ++ ".") `isPrefixOf` name || arg == name
            ]
      unless (null matching) $ do
        emitLn st =<< cDim st "-- declared in this session:"
        mapM_ (emitLn st) matching
 where
  -- a leading '@' (pasted from :t @f output) is meaningless here; drop it
  arg = dropWhile (== '@') (trim rawArg)
  nameComponents = splitOn '.' arg

-- Names bound by a history entry, parsed textually (namespace blocks are not
-- tracked; names are reported as typed).
sessionDeclNames :: String -> [String]
sessionDeclNames entry =
  [ name
  | line <- lines entry
  , Just name <- [declName (words (stripAttrs line))]
  ]
 where
  stripAttrs l = case dropWhile isSpace l of
    '@' : '[' : rest -> drop 1 (dropWhile (/= ']') rest)
    other -> other

  modifiers =
    [ "private", "protected", "noncomputable", "partial", "unsafe"
    , "scoped", "local", "mutual" ]
  binders =
    [ "def", "theorem", "lemma", "abbrev", "inductive", "structure"
    , "class", "instance", "axiom", "opaque", "example" ]

  declName (w : rest)
    | w `elem` modifiers = declName rest
    | w `elem` binders, name : _ <- rest
    , isIdentStart name, w /= "example"
    , not ("\171it!" `isPrefixOf` name) = Just (takeWhile isIdentChar name)
  declName _ = Nothing

  isIdentStart s = case s of
    c : _ -> not (c `elem` "({[:=")
    [] -> False
  isIdentChar c = not (isSpace c) && c `notElem` "({[:="

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

-- Interactive prove mode ------------------------------------------------------

proveHelp :: String
proveHelp = unlines
  [ ""
  , "Prove mode: every input line is a tactic applied to the current goals."
  , ""
  , "  :goals             reprint the current goals"
  , "  :undo [N]          take back the last N tactics (default 1)"
  , "  :script            show the tactic script so far"
  , "  :auto              try common finishing tactics on the current goal"
  , "  :qed [NAME]        finish - save as `theorem NAME` in the session"
  , "  :abort             leave prove mode (the script is printed, not lost)"
  , "  :help              this help;  :quit exits the REPL"
  , ""
  , "Tip: `exact?`, `simp?`, `rw?` record the tactic they *found* in the"
  , "script, not the question mark form."
  ]

autoTactics :: [String]
autoTactics = ["rfl", "trivial", "decide", "simp", "omega", "exact?", "aesop"]

respGoals :: JValue -> [String]
respGoals v = fromMaybe [] $ do
  gs <- jLookup "goals" v >>= jArray
  pure [g | Just g <- map jString gs]

respProofState :: JValue -> Maybe Integer
respProofState v = jLookup "proofState" v >>= jInt

formatGoals :: St -> [String] -> IO ()
formatGoals st goals
  | null goals = emitLn st =<< color st "32" "All goals accomplished \127881"
  | otherwise = do
      let n = length goals
      forM_ (zip [1 :: Int ..] goals) $ \(i, g) -> do
        when (n > 1) $
          emitLn st =<< cDim st ("\8212 goal " ++ show i ++ " of " ++ show n ++ " \8212")
        forM_ (lines (trimEnd' g)) $ \line ->
          if "case " `isPrefixOf` line
            then emitLn st =<< cCyan st line
            else if "\8866" `isPrefixOf` line
              then emitLn st =<< cBold st line
              else emitLn st line
 where
  trimEnd' = reverse . dropWhile isSpace . reverse

parseTryThis :: [(String, String)] -> Maybe String
parseTryThis messages = listToMaybe'
  [ intercalate "\n" cleaned
  | (sev, d) <- messages, sev == "info"
  , "Try this:" `isPrefixOf` dropWhile isSpace d
  , let cleaned = [ stripMarker (trim ln)
                  | ln <- drop 1 (lines d), not (null (trim ln)) ]
  , not (null cleaned)
  ]
 where
  listToMaybe' (x : _) = Just x
  listToMaybe' [] = Nothing
  stripMarker ln = case ln of
    '[' : rest -> case break (== ']') rest of
      (_, ']' : ' ' : suggestion) -> suggestion
      (_, ']' : suggestion) -> suggestion
      _ -> ln
    _ -> ln

proveScript :: ProveState -> [String]
proveScript pv = reverse [e | (_, _, Just e) <- pvStack pv]

proveEmergencyExit :: St -> String -> IO ()
proveEmergencyExit st why = do
  state <- readIORef st
  forM_ (rsProve state) $ \pv -> do
    emitLn st =<< cRed st why
    let script = proveScript pv
    unless (null script) $ do
      emitLn st =<< cDim st "tactic script so far (proof states were lost):"
      forM_ script $ \t -> emitLn st ("  " ++ t)
  modifyIORef' st (\s -> s { rsProve = Nothing })

cmdProve :: St -> String -> IO ()
cmdProve st rawArg = do
  state <- readIORef st
  case rsProve state of
    Just _ -> emitLn st =<< cRed st
      "already in prove mode \8212 :abort or :qed first"
    Nothing -> do
      let arg = substIt (rsItCounter state) (trim rawArg)
      entered <- if not (null arg)
        then do
          result <- runCmd st (rsEnv state)
            ("example : (" ++ arg ++ ") := by sorry")
          case result of
            Left err -> False <$ (emitLn st =<< cRed st err)
            Right v -> do
              let errs = [d | (s, d) <- respMessages v, s == "error"]
              case respSorries v of
                ((Just ps, goal) : _) | null errs -> do
                  modifyIORef' st (\s -> s { rsProve = Just (ProveState
                    (Just arg) [(ps, [goal], Nothing)]) })
                  pure True
                _ -> do
                  forM_ errs $ \e ->
                    emitLn st . (++ e) =<< cRed st "error: "
                  when (null errs) $ emitLn st =<< cRed st
                    "could not create a proof state \8212 is the statement a proposition?"
                  pure False
        else case rsLastSorry state of
          Just (ps, goal) -> do
            modifyIORef' st (\s -> s { rsProve = Just (ProveState
              Nothing [(ps, [goal], Nothing)]) })
            emitLn st =<< cDim st
              ("resuming from the last `sorry` \8212 on :qed the script is "
               ++ "printed for you to paste")
            pure True
          Nothing -> False <$ (emitLn st =<< cRed st
            "usage: :prove PROPOSITION   (or :prove after a `sorry`)")
      when entered $ do
        emitLn st =<< cDim st
          "entering prove mode \8212 type tactics; :help for commands"
        stateNow <- readIORef st
        forM_ (rsProve stateNow) $ \pv ->
          case pvStack pv of
            (_, goals, _) : _ -> formatGoals st goals
            [] -> pure ()

-- Apply one tactic; returns True if the proof state advanced.
applyTactic :: St -> Bool -> String -> IO Bool
applyTactic st quiet tactic = do
  state <- readIORef st
  case rsProve state of
    Nothing -> pure False
    Just pv -> case pvStack pv of
      [] -> pure False
      (ps, _, _) : _ -> do
        result <- runTactic st ps tactic
        case result of
          Left err -> do
            proveEmergencyExit st ("the backend failed: " ++ err)
            pure False
          Right v
            | Just fatal <- respFatal v -> do
                let cleaned = case lines (trim fatal) of
                      ("Lean error:" : rest@(_ : _)) -> intercalate "\n" rest
                      _ | null (trim fatal) -> "the tactic failed to elaborate"
                        | otherwise -> trim fatal
                unless quiet $ emitLn st . (++ cleaned) =<< cRed st "error: "
                pure False
            | errs@(_ : _) <- [d | (s, d) <- respMessages v, s == "error"] -> do
                unless quiet $ forM_ errs $ \e ->
                  emitLn st . (++ trimEnd' e) =<< cRed st "error: "
                pure False
            | Just newPs <- respProofState v -> do
                let entry = fromMaybe tactic (parseTryThis (respMessages v))
                when (entry /= tactic && not quiet) $
                  emitLn st =<< cDim st ("recorded as: " ++ headLine entry)
                unless quiet $
                  forM_ [d | (s, d) <- respMessages v, s == "warning"] $ \w ->
                    emitLn st . (++ trimEnd' w) =<< cYellow st "warning: "
                modifyIORef' st (\s -> s { rsProve = Just pv
                  { pvStack = (newPs, respGoals v, Just entry) : pvStack pv } })
                pure True
            | otherwise -> do
                unless quiet $ emitLn st =<< cRed st
                  "the tactic produced no new proof state"
                pure False
 where
  headLine t = case lines t of
    l : _ -> l
    [] -> t
  trimEnd' = reverse . dropWhile isSpace . reverse

currentGoals :: St -> IO [String]
currentGoals st = do
  state <- readIORef st
  pure $ case rsProve state of
    Just pv | (_, goals, _) : _ <- pvStack pv -> goals
    _ -> []

-- Handle one input line in prove mode. Returns False to exit the REPL.
proveInput :: St -> String -> IO Bool
proveInput st text = do
  let stripped = trim text
  if null stripped then pure True
  else if ":" `isPrefixOf` stripped && not (":=" `isPrefixOf` stripped)
    then do
      let (word, rest) = break isSpace (drop 1 stripped)
          arg = trim rest
      case word of
        w | w `elem` ["q", "quit", "exit"] -> pure False
        w | w `elem` ["h", "help", "?"] -> True <$ emit st proveHelp
        "goals" -> True <$ (formatGoals st =<< currentGoals st)
        "undo" -> do
          let n = if all (`elem` "0123456789") arg && not (null arg)
                then read arg else 1 :: Int
          popped <- popTactics n
          if popped == 0
            then emitLn st =<< cRed st "nothing to undo"
            else formatGoals st =<< currentGoals st
          pure True
        "script" -> do
          state <- readIORef st
          case rsProve state of
            Just pv | script@(_ : _) <- proveScript pv ->
              mapM_ (emitLn st) script
            _ -> emitLn st =<< cDim st "(no tactics yet)"
          pure True
        "auto" -> True <$ cmdAuto st
        "qed" -> True <$ cmdQed st arg
        "abort" -> do
          state <- readIORef st
          forM_ (rsProve state) $ \pv -> do
            let script = proveScript pv
            if null script
              then emitLn st =<< cDim st "left prove mode"
              else do
                emitLn st =<< cDim st "left prove mode; the script was:"
                forM_ script $ \t -> emitLn st ("  " ++ t)
          modifyIORef' st (\s -> s { rsProve = Nothing })
          pure True
        _ -> do
          emitLn st =<< cRed st ("no :" ++ word ++ " inside prove mode \8212 "
            ++ "tactics, :goals, :undo, :script, :auto, :qed, :abort, :quit")
          pure True
    else do
      counter <- rsItCounter <$> readIORef st
      advanced <- applyTactic st False (substIt counter stripped)
      when advanced $ do
        goals <- currentGoals st
        formatGoals st goals
        when (null goals) $
          emitLn st =<< cDim st "finish with :qed [NAME], inspect with :script"
      pure True
 where
  popTactics n = go n 0
   where
    go 0 acc = pure acc
    go k acc = do
      state <- readIORef st
      case rsProve state of
        Just pv | (_, _, Just entry) : rest <- pvStack pv -> do
          modifyIORef' st (\s -> s { rsProve = Just pv { pvStack = rest } })
          emitLn st =<< cDim st ("undid: " ++ takeWhile (/= '\n') entry)
          go (k - 1) (acc + 1)
        _ -> pure acc

cmdAuto :: St -> IO ()
cmdAuto st = do
  before <- length <$> currentGoals st
  go before autoTactics []
 where
  go _ [] tried = emitLn st . (++ dimTried tried "") =<< cRed st "no luck \8212 "
  go before (tac : rest) tried = do
    stillActive <- rsProve <$> readIORef st
    case stillActive of
      Nothing -> pure ()  -- emergency exit fired
      Just _ -> do
        advanced <- applyTactic st True tac
        if not advanced then go before rest (tried ++ [tac])
        else do
          goals <- currentGoals st
          if length goals < before || null goals
            then do
              state <- readIORef st
              let entry = case rsProve state of
                    Just pv | (_, _, Just e) : _ <- pvStack pv -> e
                    _ -> tac
              closed <- color st "32" ("closed by: " ++ takeWhile (/= '\n') entry)
              note <- cDim st ("  (tried "
                ++ intercalate ", " (tried ++ [tac]) ++ ")")
              emitLn st (closed ++ note)
              formatGoals st goals
              when (null goals) $
                emitLn st =<< cDim st "finish with :qed [NAME]"
            else do
              -- advanced without closing a goal: take it back
              modifyIORef' st $ \s -> s { rsProve = case rsProve s of
                Just pv | _ : rest' <- pvStack pv -> Just pv { pvStack = rest' }
                other -> other }
              go before rest (tried ++ [tac])
  dimTried tried extra = "tried " ++ intercalate ", " (tried ++ [extra | not (null extra)])

cmdQed :: St -> String -> IO ()
cmdQed st arg = do
  goals <- currentGoals st
  state <- readIORef st
  case rsProve state of
    Nothing -> pure ()
    Just pv
      | not (null goals) -> emitLn st =<< cRed st
          (show (length goals) ++ " goal"
           ++ (if length goals > 1 then "s" else "")
           ++ " remain \8212 :goals to see them, :abort to give up")
      | otherwise -> do
          let script = proveScript pv
              body = if null script then "by trivial"
                else "by\n" ++ intercalate "\n"
                  ["  " ++ ln | t <- script, ln <- lines t]
          when (any ("sorry" `isInfixOf`) script) $
            emitLn st . (++ "the script contains `sorry`")
              =<< cYellow st "warning: "
          case pvStmt pv of
            Nothing -> do
              emitLn st =<< cDim st
                "replace the `sorry` in the original declaration with:"
              emitLn st body
              modifyIORef' st (\s -> s { rsProve = Nothing })
            Just stmt -> do
              let name = if null (trim arg)
                    then "prove_" ++ show (rsProveCounter state + 1)
                    else trim arg
                  code = "theorem " ++ name ++ " : (" ++ stmt ++ ") := " ++ body
              result <- runCmd st (rsEnv state) code
              case result of
                Left err -> do
                  emitLn st =<< cRed st err
                  emitLn st =<< cRed st
                    "could not save the theorem \8212 still in prove mode"
                Right v -> do
                  errored <- printResponse st Nothing v
                  if errored
                    then emitLn st =<< cRed st
                      "could not save the theorem \8212 still in prove mode (:script to inspect)"
                    else do
                      advanceEnv st (respEnv v) code
                      when (null (trim arg)) $ modifyIORef' st
                        (\s -> s { rsProveCounter = rsProveCounter s + 1 })
                      saved <- color st "32"
                        ("saved: theorem " ++ name ++ " : " ++ stmt)
                      emitLn st saved
                      modifyIORef' st (\s -> s { rsProve = Nothing })

-- Main loop -----------------------------------------------------------------

banner :: String
banner = unlines
  [ ""
  , "   __                  __"
  , "  / /  ___ ___ ____   / /_"
  , " / /__/ -_) _ `/ _ \\_/ __/"
  , "/____/\\__/\\_,_/_//_/ \\__/"
  ]

replLoop :: St -> InputT IO ()
replLoop st = do
  step <- handleInterrupt onInterrupt $ withInterrupt $ do
    input <- readLogicalInput st
    case input of
      Nothing -> do
        liftIO (emitLn st =<< cDim st "goodbye")
        pure False
      Just text -> do
        proving <- liftIO (isJust . rsProve <$> readIORef st)
        case () of
          _ | null (trim text) -> pure True
            | proving -> liftIO (proveInput st text)
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
      proveEmergencyExit st "the interrupt discards proof states"
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
readLine :: St -> Bool -> String -> InputT IO (Maybe String)
readLine st isMain promptText = do
  interactive <- liftIO (rsInteractive <$> readIORef st)
  if interactive
    then do
      input <- getInputLine promptText
      forM_ input (liftIO . transcriptInput' st isMain promptText)
      pure input
    else do
      liftIO $ do
        state <- readIORef st
        when (rsTimestamps state && isMain) $
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
  next <- readLine st False contPrompt
  case next of
    Nothing -> pure (reverse acc)
    Just l
      | null (trim l) -> pure (reverse acc)
      | otherwise -> readContinuationLines st (l : acc)

-- One logical (possibly multi-line) input; Nothing on EOF.
readLogicalInput :: St -> InputT IO (Maybe String)
readLogicalInput st = do
  promptText <- liftIO (promptOf st)
  input <- readLine st True promptText
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
    next <- readLine st False contPrompt
    case next of
      Nothing -> pure (intercalate "\n" (reverse acc))
      Just l
        | trim l == ":}" -> pure (intercalate "\n" (reverse acc))
        | otherwise -> collectBlock (l : acc)

mkSettings :: St -> Settings IO
mkSettings st = Settings
  { complete = completeWord Nothing " \t()[]{},\10216\10217" completer
  , historyFile = Nothing  -- set in main
  , autoAddHistory = True
  }
 where
  completer word
    | ":" `isPrefixOf` word =
        pure [simpleCompletion c | c <- commandNames, word `isPrefixOf` c]
    | length word >= 2 = do
        result <- try (completionCandidates st word)
        case result of
          Right cands -> pure (map simpleCompletion cands)
          Left e -> const (pure []) (e :: SomeException)
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
  [ "usage: leant [FILE] [options]"
  , "  --project DIR    path to a Lake project to run inside"
  , "  --plain          do not use any Lake project (backend project only)"
  , "  -i, --import M   module to import at startup (repeatable)"
  , "  --timeout N      per-command timeout in seconds (0 = none, default 300)"
  , "  --time           show per-command timing"
  , "  --transcript [F] record a full transcript of the session"
  , "  --timestamps     timestamp each command in the transcript"
  , "  --repl-exe PATH  Lean REPL backend executable (see also LEANT_BACKEND)"
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
  restoreConsole <- setupConsoleUtf8
  case parseArgs args of
    Left message -> putStrLn message >> exitWith (ExitFailure 2)
    Right opts -> run opts `finally` restoreConsole

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
      putStrLn "Build it once via the Python sibling (Tools/LeantPy), or pass"
      putStrLn "--repl-exe / set LEANT_BACKEND to a repl.exe built from"
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
        , rsProve = Nothing
        , rsProveCounter = 0
        , rsLastSorry = Nothing
        , rsItCounter = 0
        , rsComplCache = []
        , rsBrowseEnv = Nothing
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
      emitLn st ("Leant (Haskell) - a GHCi-style REPL for Lean 4.  Type "
        ++ bold1 ++ " for help, " ++ bold2 ++ " to exit.")

      forM_ (optFile opts) (cmdLoad st)

      home <- getHomeDirectory
      let settings = (mkSettings st)
            { historyFile = if interactive
                then Just (home </> ".leant_history")
                else Nothing }
          behavior = if interactive then defaultBehavior else useFileHandle stdin
      runInputTBehavior behavior settings (replLoop st)

      -- cleanup
      state <- readIORef st
      when (isJust (rsTranscript state)) (transcriptStop st)
      forM_ (rsBackend state) killBackend
