-- | The fragment translator for @:synth@ (SYNTHESIS_PROPOSAL.md, phase 1).
--
-- Translation /into/ the fragment happens on the Lean side: a @run_tac@
-- metaprogram ('serializerProgram') elaborates the goal with
-- @autoImplicit@ and walks the resulting 'Expr', emitting an
-- S-expression over the LJT core connectives.  Everything structural
-- (@->@, @And@\/@Prod@\/@PProd@, @Or@\/@Sum@\/@PSum@, @Iff@, @Not@,
-- @False@\/@Empty@\/@PEmpty@, @True@\/@Unit@\/@PUnit@, non-dependent and
-- sort-quantified foralls) is decomposed; a non-recursive, non-indexed
-- inductive applied to all of its parameters whose constructor fields
-- are explicit and non-dependent expands into a generalized sum of
-- products (phase 2); every other subterm becomes an opaque atom
-- carried by its pretty-printed spelling, so alpha-equal dependent
-- subformulas compare equal and can be transported (never analyzed).  Each atom carries a safety bit: an atom built purely from
-- universally quantified variables keeps negative verdicts sound, while
-- an atom mentioning any constant (e.g. @Nat@, @P 3@) downgrades
-- \"provably uninhabited\" to \"no term found within bounds\".
--
-- This module is deliberately Djex-free: it parses the S-expression into
-- 'Frag' and answers refusal/safety questions.  'Leant.Synth.Engine'
-- owns the narrow boundary to the synthesis engine.
module Leant.Synth.Fragment
  ( Frag (..)
  , Slot (..)
  , GoalSort (..)
  , ParsedGoal (..)
  , synthPrelude
  , serializerProgram
  , parseGoalSexp
  , fragRefusal
  , fragUnsafeAtoms
  , fragSpine
  , glivenkoSplit
  , leadingTypeArgs
  ) where

import Data.Char (isSpace)
import Data.List (nub)

-- | The LJT core fragment.  @Iff@ and @Not@ are already lowered by the
-- serializer (to a pair of arrows and an arrow to 'FBot').
data Frag
  = FArr Frag Frag
  | FProd Frag Frag
  | FSum Frag Frag
  | FTop
  | FBot
  | FAll Bool String Frag
    -- ^ forall over a sort (Type\/Prop\/Sort u); the flag is 'True' for
    -- an explicit binder (needs a lambda in the Lean term) and 'False'
    -- for an implicit\/instance one (the elaborator introduces it)
  | FVar String         -- ^ opaque type variable (auto-implicit or opened binder)
  | FAtom Bool String   -- ^ opaque atom: safe-for-refutation flag, display key
  | FInd String [(String, [Frag])]
    -- ^ expanded inductive occurrence (phase 2): display key, then one
    -- entry per constructor (full Lean name, field fragments).  Emitted
    -- only when the serializer saw the complete constructor list with
    -- non-dependent explicit fields, so the node itself never poisons a
    -- refutation; its fields answer for themselves
  | FRec String [(String, [Frag])]
    -- ^ recursive (or nested) inductive occurrence: an opaque atom for
    -- elimination, but its listed constructors are sound introduction
    -- rules the engine receives as premises.  The constructor list may
    -- be partial (only in-fragment constructors are carried), and the
    -- key always poisons refutations - structure stays hidden
  | FDepth              -- ^ translator depth bound reached
  deriving (Eq, Show)

-- | One position of the goal's leading binder spine, used to line the
-- rendered candidate's lambda binders up with the Lean goal.
data Slot
  = SlotArrow Frag      -- ^ an arrow; carries the domain fragment
  | SlotAll Bool        -- ^ a quantifier; 'True' when the binder is explicit
  deriving (Eq, Show)

data GoalSort = GoalProp | GoalType
  deriving (Eq, Show)

data ParsedGoal = ParsedGoal
  { pgSort :: GoalSort
  , pgFrag :: Frag
  }
  deriving (Eq, Show)

-- | Compiled once into the synthesis environment (session imports plus
-- @Lean@): the goal serializer as ordinary definitions.  @run_tac@ runs
-- interpreted and cannot host @let rec@, so the recursion lives in a
-- compiled @partial def@ that the per-goal command merely calls.
synthPrelude :: String
synthPrelude = unlines
  [ "namespace LeantSynth"
  , "open Lean Meta"
  , ""
  , "def esc (s : String) : String :="
  , "  \"\\\"\" ++ s.foldl (fun a c =>"
  , "    if c == '\\\"' || c == '\\\\' then a ++ \"\\\\\" ++ toString c"
  , "    else a.push c) \"\" ++ \"\\\"\""
  , ""
  , "def atomOf (e : Expr) : MetaM String := do"
  , "  let safe := e.getUsedConstants.isEmpty && !e.isSort"
  , "  let pp \8592 Meta.ppExpr e"
  , "  pure (\"(atom \" ++ (if safe then \"safe\" else \"unsafe\") ++ \" \""
  , "    ++ esc (toString pp) ++ \")\")"
  , ""
  , "mutual"
  , ""
  , "partial def go (fuel depth : Nat) (blocked : List String) (e : Expr)"
  , "    : MetaM String := do"
  , "  match fuel with"
  , "  | 0 => pure \"(depth)\""
  , "  | Nat.succ fuel => do"
  , "    let e \8592 instantiateMVars e"
  , "    let e \8592 whnfR e.consumeMData"
  , "    if e.isSort then atomOf e"
  , "    else match e with"
  , "    | Expr.fvar _ => do"
  , "      let t \8592 whnfR (\8592 inferType e)"
  , "      if t.isSort then"
  , "        pure (\"(var \" ++ esc (toString (\8592 Meta.ppExpr e)) ++ \")\")"
  , "      else atomOf e"
  , "    | Expr.forallE _ t b bi =>"
  , "      if b.hasLooseBVars then do"
  , "        let ts \8592 whnfR t"
  , "        if ts.isSort then"
  , "          withLocalDeclD (Name.mkSimple (\"s\" ++ toString depth)) t"
  , "              fun fv => do"
  , "            let inner \8592 go fuel (depth + 1) blocked (b.instantiate1 fv)"
  , "            let tag := if bi.isExplicit then \"(all \" else \"(alli \""
  , "            pure (tag ++ esc (\"s\" ++ toString depth) ++ \" \""
  , "              ++ inner ++ \")\")"
  , "        else atomOf e"
  , "      else if bi.isExplicit then do"
  , "        let d \8592 go fuel depth blocked t"
  , "        let r \8592 go fuel depth blocked b"
  , "        pure (\"(-> \" ++ d ++ \" \" ++ r ++ \")\")"
  , "      else do"
  , "        -- an unused implicit binder is introduced by the elaborator,"
  , "        -- so the term neither binds nor applies it"
  , "        let r \8592 go fuel depth blocked b"
  , "        pure (\"(alli \" ++ esc (\"i\" ++ toString depth) ++ \" \""
  , "          ++ r ++ \")\")"
  , "    | _ =>"
  , "      match e.getAppFn with"
  , "      | Expr.const n _ => do"
  , "        let args := e.getAppArgs"
  , "        let bin (tag : String) : MetaM String := do"
  , "          let a \8592 go fuel depth blocked args[0]!"
  , "          let b \8592 go fuel depth blocked args[1]!"
  , "          pure (\"(\" ++ tag ++ \" \" ++ a ++ \" \" ++ b ++ \")\")"
  , "        if args.size == 0 &&"
  , "            (n == ``False || n == ``Empty || n == ``PEmpty) then"
  , "          pure \"(bot)\""
  , "        else if args.size == 0 &&"
  , "            (n == ``True || n == ``Unit || n == ``PUnit) then"
  , "          pure \"(top)\""
  , "        else if args.size == 2 &&"
  , "            (n == ``And || n == ``Prod || n == ``PProd) then"
  , "          bin \"prod\""
  , "        else if args.size == 2 &&"
  , "            (n == ``Or || n == ``Sum || n == ``PSum) then"
  , "          bin \"sum\""
  , "        else if args.size == 2 && n == ``Iff then do"
  , "          let a \8592 go fuel depth blocked args[0]!"
  , "          let b \8592 go fuel depth blocked args[1]!"
  , "          pure (\"(prod (-> \" ++ a ++ \" \" ++ b ++ \") (-> \""
  , "            ++ b ++ \" \" ++ a ++ \"))\")"
  , "        else if args.size == 1 && n == ``Not then do"
  , "          let a \8592 go fuel depth blocked args[0]!"
  , "          pure (\"(-> \" ++ a ++ \" (bot))\")"
  , "        else do"
  , "          match \8592 indOf fuel depth blocked e with"
  , "          | some s => pure s"
  , "          | none =>"
  , "            match \8592 recOf fuel depth blocked e with"
  , "            | some s => pure s"
  , "            | none => atomOf e"
  , "      | _ => atomOf e"
  , ""
  , "-- Phase 2: a non-recursive, non-indexed, non-mutual, non-nested"
  , "-- inductive applied to all of its parameters expands into a"
  , "-- generalized sum of products, provided every constructor field is"
  , "-- explicit and non-dependent; anything else falls back to an atom."
  , "partial def indOf (fuel depth : Nat) (blocked : List String) (e : Expr)"
  , "    : MetaM (Option String) := do"
  , "  match e.getAppFn with"
  , "  | Expr.const n us =>"
  , "    match (\8592 getEnv).find? n with"
  , "    | some (ConstantInfo.inductInfo iv) =>"
  , "      if iv.numIndices != 0 || iv.isRec || iv.isNested"
  , "          || iv.isUnsafe || iv.all.length != 1"
  , "          || e.getAppNumArgs != iv.numParams then"
  , "        pure none"
  , "      else do"
  , "        let args := e.getAppArgs"
  , "        let mut ctors := \"\""
  , "        for c in iv.ctors do"
  , "          let ct \8592 inferType (mkAppN (Expr.const c us) args)"
  , "          match \8592 ctorFields fuel depth blocked ct with"
  , "          | none => return none"
  , "          | some fs =>"
  , "            ctors := ctors ++ \" (ctor \" ++ esc c.toString ++ fs ++ \")\""
  , "        let pp \8592 Meta.ppExpr e"
  , "        pure (some (\"(ind \" ++ esc (toString pp) ++ ctors ++ \")\"))"
  , "    | _ => pure none"
  , "  | _ => pure none"
  , ""
  , "-- A recursive (or nested) inductive stays an opaque atom for"
  , "-- elimination, but its constructors are still sound introduction"
  , "-- rules: emit the ones whose instantiated fields are explicit and"
  , "-- non-dependent, with this occurrence's own key blocked so field"
  , "-- occurrences of the type serialize as the matching atom."
  , "partial def recOf (fuel depth : Nat) (blocked : List String) (e : Expr)"
  , "    : MetaM (Option String) := do"
  , "  match e.getAppFn with"
  , "  | Expr.const n us =>"
  , "    match (\8592 getEnv).find? n with"
  , "    | some (ConstantInfo.inductInfo iv) =>"
  , "      if iv.numIndices != 0 || !(iv.isRec || iv.isNested)"
  , "          || iv.isUnsafe || iv.all.length != 1"
  , "          || e.getAppNumArgs != iv.numParams then"
  , "        pure none"
  , "      else do"
  , "        let pp \8592 Meta.ppExpr e"
  , "        let key := toString pp"
  , "        if blocked.contains key then pure none"
  , "        else do"
  , "          let args := e.getAppArgs"
  , "          let blocked := key :: blocked"
  , "          let mut ctors := \"\""
  , "          let mut found := false"
  , "          for c in iv.ctors do"
  , "            let ct \8592 inferType (mkAppN (Expr.const c us) args)"
  , "            match \8592 ctorFields fuel depth blocked ct with"
  , "            | none => pure ()"
  , "            | some fs =>"
  , "              found := true"
  , "              ctors := ctors ++ \" (ctor \" ++ esc c.toString"
  , "                ++ fs ++ \")\""
  , "          if !found then pure none"
  , "          else pure (some (\"(rec \" ++ esc key ++ ctors ++ \")\"))"
  , "    | _ => pure none"
  , "  | _ => pure none"
  , ""
  , "partial def ctorFields (fuel depth : Nat) (blocked : List String)"
  , "    (t : Expr)"
  , "    : MetaM (Option String) := do"
  , "  let t \8592 whnfR t"
  , "  match t with"
  , "  | Expr.forallE _ dom body bi =>"
  , "    if body.hasLooseBVars || !bi.isExplicit then pure none"
  , "    else do"
  , "      let d \8592 go fuel depth blocked dom"
  , "      match \8592 ctorFields fuel depth blocked body with"
  , "      | none => pure none"
  , "      | some rest => pure (some (\" \" ++ d ++ rest))"
  , "  | _ => pure (some \"\")"
  , ""
  , "end"
  , ""
  , "end LeantSynth"
  ]

-- | The per-goal Lean command run in the synthesis environment.  The
-- goal text is spliced verbatim between parentheses; elaboration errors
-- surface as ordinary error messages and become the honest refusal.  The
-- trailing @sorry@ closes the example; its sorry entry is ignored by the
-- caller.
serializerProgram :: String -> String
serializerProgram goal = unlines
  [ "open Lean Meta Elab Tactic in"
  , "set_option autoImplicit true in"
  , "set_option linter.unusedVariables false in"
  , "example : (" ++ goal ++ ") := by"
  , "  run_tac withMainContext do"
  , "    let tgt \8592 getMainTarget"
  , "    let isP \8592 Meta.isProp tgt"
  , "    let s \8592 LeantSynth.go 100 0 [] tgt"
  , "    logInfo (\"(goal \" ++ (if isP then \"prop\" else \"type\")"
  , "      ++ \" \" ++ s ++ \")\")"
  , "  sorry"
  ]

-- S-expression parsing ------------------------------------------------------

data Tok = TL | TR | TSym String | TStr String
  deriving (Eq, Show)

tokenize :: String -> Either String [Tok]
tokenize [] = Right []
tokenize (c : rest)
  | isSpace c = tokenize rest
  | c == '(' = (TL :) <$> tokenize rest
  | c == ')' = (TR :) <$> tokenize rest
  | c == '"' = do
      (lit, rest') <- str rest
      (TStr lit :) <$> tokenize rest'
  | otherwise =
      let (word, rest') = break (\x -> isSpace x || x `elem` "()\"") (c : rest)
      in (TSym word :) <$> tokenize rest'
 where
  str ('\\' : x : xs) = do
    (a, b) <- str xs
    pure (x : a, b)
  str ('"' : xs) = pure ("", xs)
  str (x : xs) = do
    (a, b) <- str xs
    pure (x : a, b)
  str [] = Left "unterminated string in goal translation"

-- | Parse the serializer's @(goal SORT FRAG)@ message.
parseGoalSexp :: String -> Either String ParsedGoal
parseGoalSexp text = do
  toks <- tokenize text
  case toks of
    TL : TSym "goal" : TSym sort : rest -> do
      gs <- case sort of
        "prop" -> Right GoalProp
        "type" -> Right GoalType
        other -> Left ("unknown goal sort " ++ other)
      (frag, rest') <- parseFrag rest
      case rest' of
        [TR] -> Right (ParsedGoal gs frag)
        _ -> Left "trailing tokens in goal translation"
    _ -> Left "malformed goal translation"

parseFrag :: [Tok] -> Either String (Frag, [Tok])
parseFrag (TL : TSym tag : rest) = case tag of
  "->" -> binary FArr rest
  "prod" -> binary FProd rest
  "sum" -> binary FSum rest
  "top" -> nullary FTop rest
  "bot" -> nullary FBot rest
  "depth" -> nullary FDepth rest
  "var" -> case rest of
    TStr name : TR : rest' -> Right (FVar name, rest')
    _ -> Left "malformed (var ...)"
  "atom" -> case rest of
    TSym safety : TStr key : TR : rest' -> do
      safe <- case safety of
        "safe" -> Right True
        "unsafe" -> Right False
        other -> Left ("unknown atom safety " ++ other)
      Right (FAtom safe key, rest')
    _ -> Left "malformed (atom ...)"
  "all" -> allTag True rest
  "alli" -> allTag False rest
  "ind" -> case rest of
    TStr key : rest' -> do
      (ctors, rest'') <- parseCtors rest'
      Right (FInd key ctors, rest'')
    _ -> Left "malformed (ind ...)"
  "rec" -> case rest of
    TStr key : rest' -> do
      (ctors, rest'') <- parseCtors rest'
      Right (FRec key ctors, rest'')
    _ -> Left "malformed (rec ...)"
  other -> Left ("unknown fragment tag " ++ other)
 where
  parseCtors (TR : toks) = Right ([], toks)
  parseCtors (TL : TSym "ctor" : TStr name : toks) = do
    (fields, toks') <- parseFields toks
    (rest', toks'') <- parseCtors toks'
    Right ((name, fields) : rest', toks'')
  parseCtors _ = Left "malformed (ctor ...)"
  parseFields (TR : toks) = Right ([], toks)
  parseFields toks = do
    (field, toks') <- parseFrag toks
    (fields, toks'') <- parseFields toks'
    Right (field : fields, toks'')
  binary ctor toks = do
    (a, toks') <- parseFrag toks
    (b, toks'') <- parseFrag toks'
    close (ctor a b) toks''
  nullary value toks = close value toks
  allTag explicit toks = case toks of
    TStr name : toks' -> do
      (body, toks'') <- parseFrag toks'
      close (FAll explicit name body) toks''
    _ -> Left "malformed (all ...)"
  close value (TR : toks) = Right (value, toks)
  close _ _ = Left "expected ) in goal translation"
parseFrag _ = Left "expected ( in goal translation"

-- Fragment analysis ---------------------------------------------------------

-- | An honest refusal, when the goal offers the engine nothing structural
-- to work with, with the reason.
fragRefusal :: Frag -> Maybe String
fragRefusal frag
  | hasDepth frag = Just
      "the goal exceeds the translator's depth bound"
  | FAtom _ key <- peel frag = Just
      ("the goal is a single opaque atom `" ++ key
       ++ "` \8212 :synth handles \8594/\215/\8853/\8704/\8869/\8868 over \
          \opaque variables; dependent or non-propositional structure is \
          \transported, never analyzed")
  | otherwise = Nothing
 where
  peel (FAll _ _ b) = peel b
  peel f = f
  hasDepth f = case f of
    FArr a b -> hasDepth a || hasDepth b
    FProd a b -> hasDepth a || hasDepth b
    FSum a b -> hasDepth a || hasDepth b
    FAll _ _ b -> hasDepth b
    FInd _ ctors -> any (any hasDepth . snd) ctors
    FRec _ ctors -> any (any hasDepth . snd) ctors
    FDepth -> True
    _ -> False

-- | The goal's leading binder spine (arrows and quantifiers, stopping
-- at the first other connective).  Djinn models quantifiers as implicit
-- polymorphism and its candidates bind only arrows; the renderer weaves
-- anonymous binders for explicit quantifier slots into the candidate's
-- lambda, and skips implicit ones (Lean introduces those itself).
fragSpine :: Frag -> [Slot]
fragSpine (FArr dom body) = SlotArrow dom : fragSpine body
fragSpine (FAll explicit _ body) = SlotAll explicit : fragSpine body
fragSpine _ = []

-- | How many explicit type arguments a value of this type needs before
-- its term arguments (its leading explicit sort-quantifiers).  Used to
-- render applications of quantified hypotheses as @f _ x@: Djinn's
-- instantiation evidence is the bare hypothesis, but Lean's explicit
-- binders demand a placeholder for the elaborator to infer.
leadingTypeArgs :: Frag -> Int
leadingTypeArgs (FAll True _ body) = 1 + leadingTypeArgs body
leadingTypeArgs (FAll False _ body) = leadingTypeArgs body
leadingTypeArgs _ = 0

-- | Split a goal into its leading quantifier prefix and a
-- quantifier-free body, when it has that shape.  This is the fragment
-- where the Glivenko classical fallback is complete: for propositional
-- @body@ (the prefix variables are opaque atoms to the engine either
-- way), @body@ is classically provable exactly when @\172\172body@ is
-- intuitionistically provable.  Each prefix entry carries the binder's
-- explicitness.
glivenkoSplit :: Frag -> Maybe ([(Bool, String)], Frag)
glivenkoSplit = go []
 where
  go acc (FAll explicit binder body) = go ((explicit, binder) : acc) body
  go acc body
    | quantFree body = Just (reverse acc, body)
    | otherwise = Nothing
  quantFree f = case f of
    FArr a b -> quantFree a && quantFree b
    FProd a b -> quantFree a && quantFree b
    FSum a b -> quantFree a && quantFree b
    FInd _ ctors -> all (all quantFree . snd) ctors
    FRec _ ctors -> all (all quantFree . snd) ctors
    FAll{} -> False
    _ -> True

-- | Display keys of atoms that poison a negative verdict (they mention
-- concrete constants whose structure the engine cannot see).
fragUnsafeAtoms :: Frag -> [String]
fragUnsafeAtoms = nub . go
 where
  go f = case f of
    FArr a b -> go a ++ go b
    FProd a b -> go a ++ go b
    FSum a b -> go a ++ go b
    FAll _ _ b -> go b
    FInd _ ctors -> concatMap (concatMap go . snd) ctors
    FRec key ctors -> key : concatMap (concatMap go . snd) ctors
    FAtom False key -> [key]
    _ -> []
