-- | Output beautification for :info (port of format_info / indent_def_body).
module LeanRepl.Format
  ( formatInfo
  , indentDefBody
  ) where

import Data.Char (isSpace)
import Data.List (isPrefixOf, isSuffixOf, stripPrefix)
import Data.Maybe (fromMaybe)

-- | Reformat @#print@ output for inductives/structures/classes as a valid
-- Lean declaration; Nothing when the text is not in that shape.
formatInfo :: String -> Maybe String
formatInfo text = do
  let ls = lines text
  nparamsIdx <- indexOfNumberOfParameters ls
  if nparamsIdx == 0 then Nothing else Just ()
  let header = take nparamsIdx ls
  headerFirst <- case header of
    h : _ -> Just h
    [] -> Nothing
  fullName <- declaredName headerFirst
  let prefixDot = fullName ++ "."
      stripQual s = fromMaybe s (stripPrefix prefixDot s)
      body = drop (nparamsIdx + 1) ls
  sections <- collect stripQual body emptySections
  let headerOut = init header ++ [last header ++ " where"]
      ctorLine = case secCtor sections of
        Just name | name /= "mk" -> ["  " ++ name ++ " ::"]
        _ -> []
  pure $ unlines' $ headerOut
    ++ ctorLine
    ++ map ("  " ++) (secCtors sections)
    ++ map ("  " ++) (secFields sections)
 where
  unlines' = foldr1 (\a b -> a ++ "\n" ++ b)

data Sections = Sections
  { secCtors :: [String]
  , secFields :: [String]
  , secCtor :: Maybe String
  }

emptySections :: Sections
emptySections = Sections [] [] Nothing

indexOfNumberOfParameters :: [String] -> Maybe Int
indexOfNumberOfParameters ls = lookup True (zip matches [0 ..])
 where
  matches = map isNumberOfParameters ls
  isNumberOfParameters ln = case stripPrefix "number of parameters: " (trim ln) of
    Just digits -> not (null digits) && all (`elem` "0123456789") digits
    Nothing -> False

declaredName :: String -> Maybe String
declaredName headerLine = do
  rest <- stripAnyPrefix
    ["class inductive ", "inductive ", "structure ", "class "]
    headerLine
  let token = takeWhile (`notElem` " ({:") rest
      name = dropWhileEnd' (== '.') token
  if null name then Nothing else Just name
 where
  stripAnyPrefix prefixes s =
    case [r | p <- prefixes, Just r <- [stripPrefix p s]] of
      r : _ -> Just r
      [] -> Nothing
  dropWhileEnd' p = reverse . dropWhile p . reverse

collect :: (String -> String) -> [String] -> Sections -> Maybe Sections
collect stripQual = go Nothing
 where
  go _ [] acc = Just acc
    { secCtors = reverse (secCtors acc)
    , secFields = reverse (secFields acc)
    }
  go section (ln : rest) acc
    | s == "constructors:" = go (Just CtorsSec) rest acc
    | s == "fields:" = go (Just FieldsSec) rest acc
    | s == "constructor:" = go (Just CtorSec) rest acc
    | null s = go section rest acc
    | otherwise = case section of
        Just CtorsSec
          | " " `isPrefixOf` ln && not (null (secCtors acc)) ->
              go section rest acc { secCtors = ("    " ++ s) : secCtors acc }
          | otherwise ->
              go section rest acc { secCtors = ("| " ++ stripQual s) : secCtors acc }
        Just FieldsSec
          | "   " `isPrefixOf` ln && not (null (secFields acc)) ->
              go section rest acc { secFields = ("  " ++ s) : secFields acc }
          | otherwise ->
              go section rest acc { secFields = stripQual s : secFields acc }
        Just CtorSec -> case secCtor acc of
          Just _ -> go section rest acc
          Nothing ->
            let name = takeWhile (`notElem` ". {") (stripQual s)
            in go section rest acc { secCtor = Just name }
        Nothing -> Nothing  -- unrecognized shape; show the original text
   where
    s = trim ln

data Section = CtorsSec | FieldsSec | CtorSec

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- | @#print@ emits definition bodies at column 0 after the ':=' line; indent
-- them two spaces, Lean-style. Nothing if the shape doesn't match.
indentDefBody :: String -> Maybe String
indentDefBody text = do
  let ls = lines text
  headerEnd <- lookup True (zip (map endsWithAssign ls) [0 ..])
  let body = drop (headerEnd + 1) ls
  if null body || all alreadyIndented body
    then Nothing
    else Just $ intercalateNL $ take (headerEnd + 1) ls
      ++ map indent body
 where
  endsWithAssign ln = ":=" `isSuffixOf` trimEnd ln
  trimEnd = reverse . dropWhile isSpace . reverse
  alreadyIndented ln = " " `isPrefixOf` ln || null (trim ln)
  indent ln = if null (trim ln) then ln else "  " ++ ln
  intercalateNL = foldr1 (\a b -> a ++ "\n" ++ b)
