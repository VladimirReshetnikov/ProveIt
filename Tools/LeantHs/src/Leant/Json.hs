-- | Minimal JSON support for the Lean REPL protocol.
--
-- The backend speaks a small, fixed JSON dialect, so this hand-rolled
-- parser/encoder replaces an aeson dependency (keeping the port buildable
-- with GHC boot libraries alone).
module Leant.Json
  ( JValue (..)
  , parseJson
  , encodeJson
  , jLookup
  , jString
  , jInt
  , jArray
  ) where

import Data.Char (chr, isDigit, isHexDigit, isSpace, ord)
import Data.List (intercalate)
import Numeric (showHex)

data JValue
  = JNull
  | JBool !Bool
  | JInt !Integer
  | JNum !Double
  | JStr String
  | JArr [JValue]
  | JObj [(String, JValue)]
  deriving (Eq, Show)

-- Accessors -----------------------------------------------------------------

jLookup :: String -> JValue -> Maybe JValue
jLookup key (JObj fields) = lookup key fields
jLookup _ _ = Nothing

jString :: JValue -> Maybe String
jString (JStr s) = Just s
jString _ = Nothing

jInt :: JValue -> Maybe Integer
jInt (JInt n) = Just n
jInt (JNum d) = Just (round d)
jInt _ = Nothing

jArray :: JValue -> Maybe [JValue]
jArray (JArr xs) = Just xs
jArray _ = Nothing

-- Encoding ------------------------------------------------------------------

encodeJson :: JValue -> String
encodeJson JNull = "null"
encodeJson (JBool b) = if b then "true" else "false"
encodeJson (JInt n) = show n
encodeJson (JNum d) = show d
encodeJson (JStr s) = encodeString s
encodeJson (JArr xs) = "[" ++ intercalate "," (map encodeJson xs) ++ "]"
encodeJson (JObj fields) =
  "{" ++ intercalate "," (map field fields) ++ "}"
 where
  field (k, v) = encodeString k ++ ":" ++ encodeJson v

encodeString :: String -> String
encodeString s = '"' : concatMap escape s ++ "\""
 where
  escape '"' = "\\\""
  escape '\\' = "\\\\"
  escape '\n' = "\\n"
  escape '\r' = "\\r"
  escape '\t' = "\\t"
  escape c
    | ord c < 0x20 = "\\u" ++ pad (showHex (ord c) "")
    | otherwise = [c]  -- non-ASCII passes through; the handle encodes UTF-8
  pad hex = replicate (4 - length hex) '0' ++ hex

-- Parsing -------------------------------------------------------------------

-- | Parse a JSON document. Returns Left with a short error description.
parseJson :: String -> Either String JValue
parseJson input = case value (dropWhile isSpace input) of
  Right (v, rest)
    | all isSpace rest -> Right v
    | otherwise -> Left ("trailing content: " ++ take 40 rest)
  Left err -> Left err

type P a = Either String (a, String)

value :: String -> P JValue
value s = case s of
  '{' : rest -> object (skip rest)
  '[' : rest -> array (skip rest)
  '"' : rest -> do
    (str, rest') <- stringBody rest
    pure (JStr str, rest')
  't' : 'r' : 'u' : 'e' : rest -> pure (JBool True, rest)
  'f' : 'a' : 'l' : 's' : 'e' : rest -> pure (JBool False, rest)
  'n' : 'u' : 'l' : 'l' : rest -> pure (JNull, rest)
  c : _ | c == '-' || isDigit c -> number s
  _ -> Left ("unexpected input: " ++ take 40 s)

skip :: String -> String
skip = dropWhile isSpace

object :: String -> P JValue
object ('}' : rest) = pure (JObj [], rest)
object s = go s []
 where
  go input acc = do
    (key, afterKey) <- case skip input of
      '"' : r -> stringBody r
      other -> Left ("expected object key at: " ++ take 40 other)
    afterColon <- case skip afterKey of
      ':' : r -> pure r
      other -> Left ("expected ':' at: " ++ take 40 other)
    (v, afterValue) <- value (skip afterColon)
    case skip afterValue of
      ',' : r -> go r ((key, v) : acc)
      '}' : r -> pure (JObj (reverse ((key, v) : acc)), r)
      other -> Left ("expected ',' or '}' at: " ++ take 40 other)

array :: String -> P JValue
array (']' : rest) = pure (JArr [], rest)
array s = go s []
 where
  go input acc = do
    (v, afterValue) <- value (skip input)
    case skip afterValue of
      ',' : r -> go (skip r) (v : acc)
      ']' : r -> pure (JArr (reverse (v : acc)), r)
      other -> Left ("expected ',' or ']' at: " ++ take 40 other)

stringBody :: String -> P String
stringBody = go id
 where
  go acc ('"' : rest) = pure (acc "", rest)
  go acc ('\\' : c : rest) = case c of
    '"' -> go (acc . ('"' :)) rest
    '\\' -> go (acc . ('\\' :)) rest
    '/' -> go (acc . ('/' :)) rest
    'b' -> go (acc . ('\b' :)) rest
    'f' -> go (acc . ('\f' :)) rest
    'n' -> go (acc . ('\n' :)) rest
    'r' -> go (acc . ('\r' :)) rest
    't' -> go (acc . ('\t' :)) rest
    'u' -> case splitAt 4 rest of
      (hex, rest')
        | length hex == 4 && all isHexDigit hex ->
            let code = read ("0x" ++ hex) :: Int
            in if code >= 0xD800 && code <= 0xDBFF
                 then case rest' of
                   -- surrogate pair
                   '\\' : 'u' : rest'' -> case splitAt 4 rest'' of
                     (hex2, rest''')
                       | length hex2 == 4 && all isHexDigit hex2 ->
                           let lo = read ("0x" ++ hex2) :: Int
                               cp = 0x10000
                                 + ((code - 0xD800) * 0x400)
                                 + (lo - 0xDC00)
                           in go (acc . (chr cp :)) rest'''
                     _ -> Left "invalid low surrogate"
                   _ -> Left "lone high surrogate"
                 else go (acc . (chr code :)) rest'
      _ -> Left "invalid \\u escape"
    _ -> Left ("invalid escape: \\" ++ [c])
  go acc (c : rest) = go (acc . (c :)) rest
  go _ [] = Left "unterminated string"

number :: String -> P JValue
number s =
  let (token, rest) = span (`elem` "-+.eE0123456789") s
  in if any (`elem` ".eE") token
       then case reads token :: [(Double, String)] of
         [(d, "")] -> pure (JNum d, rest)
         _ -> Left ("bad number: " ++ token)
       else case reads token :: [(Integer, String)] of
         [(n, "")] -> pure (JInt n, rest)
         _ -> Left ("bad number: " ++ token)
