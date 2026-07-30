-- | Input classification and multi-line continuation heuristics
-- (port of the corresponding section of leanrepl.py).
module LeanRepl.Classify
  ( isDeclaration
  , firstToken
  , needsContinuation
  , stripStringsAndComments
  , bracketBalance
  ) where

import Data.Char (isAlpha, isAlphaNum, isSpace)
import Data.List (isPrefixOf, isSuffixOf)
import qualified Data.Set as Set

declKeywords :: Set.Set String
declKeywords = Set.fromList
  [ "abbrev", "add_decl_doc", "alias", "attribute", "axiom"
  , "binder_predicate", "builtin_initialize", "class", "declare_syntax_cat"
  , "def", "deriving", "elab", "elab_rules", "end", "example", "export"
  , "extends", "gen_injective_theorems", "import", "in", "include"
  , "inductive", "infix", "infixl", "infixr", "initialize", "instance"
  , "lemma", "local", "macro", "macro_rules", "mutual", "namespace"
  , "noncomputable", "notation", "omit", "opaque", "open", "partial"
  , "postfix", "prefix", "private", "protected", "recall", "run_cmd"
  , "run_elab", "scoped", "section", "set_option", "show_panel_widgets"
  , "structure", "syntax", "theorem", "unif_hint", "universe", "unsafe"
  , "variable", "variables"
  ]

continuationEndings :: [String]
continuationEndings =
  [ ":=", "=>", "by", "do", "then", "else", "where", ",", "|", "fun"
  , "with", "\8592", "<-", "\8594", "->", "\8596", "<->", "\8743", "\8744"
  , "+", "*", "/", "(", "[", "{", "\10216", "\171", ":", ";", "\183", "$"
  , "from", "have", "let", "in", "match"
  ]

openBrackets, closeBrackets :: String
openBrackets = "([{\10216"
closeBrackets = ")]}\10217"

-- | Remove string literals, char literals, and comments so bracket counting
-- is not confused by them. Rough but adequate for balance heuristics.
stripStringsAndComments :: String -> String
stripStringsAndComments = go
 where
  go [] = []
  go ('"' : rest) = go (skipString rest)
  go ('\'' : a : b : rest)
    | a == '\\' = go (dropCharLit (b : rest))
    | b == '\'' = go rest
  go ('-' : '-' : rest) = go (dropWhile (/= '\n') rest)
  go ('/' : '-' : rest) = go (skipBlockComment (1 :: Int) rest)
  go (c : rest) = c : go rest

  skipString [] = []
  skipString ('\\' : _ : rest) = skipString rest
  skipString ('"' : rest) = rest
  skipString (_ : rest) = skipString rest

  dropCharLit ('\'' : rest) = rest
  dropCharLit (_ : rest) = dropCharLit rest
  dropCharLit [] = []

  skipBlockComment _ [] = []
  skipBlockComment depth ('/' : '-' : rest) = skipBlockComment (depth + 1) rest
  skipBlockComment depth ('-' : '/' : rest)
    | depth <= 1 = rest
    | otherwise = skipBlockComment (depth - 1) rest
  skipBlockComment depth (_ : rest) = skipBlockComment depth rest

-- | Net count of unclosed brackets.
bracketBalance :: String -> Int
bracketBalance text = sum (map score (stripStringsAndComments text))
 where
  score c
    | c `elem` openBrackets = 1
    | c `elem` closeBrackets = -1
    | otherwise = 0

inOpenBlockComment :: String -> Bool
inOpenBlockComment = go (0 :: Int)
 where
  go depth [] = depth > 0
  go depth ('/' : '-' : rest) = go (depth + 1) rest
  go depth ('-' : '/' : rest) = go (max 0 (depth - 1)) rest
  go depth (_ : rest) = go depth rest

-- | Heuristic: does this input look syntactically incomplete?
needsContinuation :: String -> Bool
needsContinuation text
  | inOpenBlockComment text = True
  | bracketBalance text > 0 = True
  | null stripped = False
  | otherwise = any triggers continuationEndings
 where
  stripped = trimEnd (stripStringsAndComments text)

  triggers ending =
    ending `isSuffixOf` stripped && not (falseAlarm ending)

  -- avoid treating identifiers ending in keyword letters as keywords
  falseAlarm ending
    | all isAlpha ending || ending `elem` ["<-", ":="] =
        case drop (length ending) (reverse stripped) of
          before : _ -> isAlphaNum before || before `elem` "_.'"
          [] -> False
    | otherwise = False

trimEnd :: String -> String
trimEnd = reverse . dropWhile isSpace . reverse

-- | First word-like token of the input (used for keyword dispatch).
firstToken :: String -> String
firstToken text = case dropWhile isSpace text of
  '#' : rest -> '#' : takeWhile isIdentChar rest
  '@' : '[' : _ -> "@["
  s -> takeWhile isIdentChar s
 where
  isIdentChar c = isAlphaNum c || c `elem` "_?!'"

-- | Should this input run verbatim as a top-level command (rather than being
-- evaluated as an expression via #eval / #check)?
isDeclaration :: String -> Bool
isDeclaration text =
  "#" `isPrefixOf` t
    || "@[" `isPrefixOf` t
    || "--" `isPrefixOf` t
    || "/-" `isPrefixOf` t
    || Set.member (firstToken t) declKeywords
 where
  t = dropWhile isSpace text
