-- | The narrow engine boundary for @:synth@ (design rule 4 of
-- SYNTHESIS_PROPOSAL.md): fragment goal in, candidate batch out.  This is
-- the only Leant module that imports Djex; the engine behind the boundary
-- (today: Djinn's LJT search, in-process) is swappable without touching
-- the REPL layer.
--
-- Verdicts follow Djex's evidence\/progress split, extended by the
-- two-axis honesty rule of the proposal: a refutation is reported as
-- sound only when Djex itself claims 'ProvedUninhabitable' (its
-- projection was complete) /and/ the Leant-side translation introduced no
-- atom that hides concrete structure ('fragUnsafeAtoms').
module Leant.Synth.Engine
  ( SynthOutcome (..)
  , synthesize
  , forceOutcome
  , candidateWindow
  ) where

import Data.List (sortOn)
import qualified Data.Map.Strict as Map

import Language.Haskell.Djex
  ( QueryEvidence (..)
  , QueryOptions (..)
  , QueryRequest (..)
  , Boxity (Boxed)
  , Completion (..)
  , Progress (..)
  , Type (..)
  , batchCandidates
  , batchProgress
  , candidateOutput
  , defaultQueryOptions
  , expressionSize
  , functionClauseExpression
  , mkDefinitionName
  , mkDjinnRequest
  , mkIdentifier
  , renderDiagnostic
  , resultEvidence
  , resultSearch
  , runDjinnQuery
  , standardDjinnSession
  , tupleName
  )

import Leant.Synth.Fragment (Frag (..), fragUnsafeAtoms)
import Leant.Synth.Render (renderLeanTerm)

-- | What the engine established for one goal.  Candidate terms are a lazy
-- ranked list of rendered variant groups (one group per engine candidate;
-- within a group, textual variants of the same term); the caller verifies
-- them against the backend before showing anything.
data SynthOutcome
  = SynthCandidates [[String]] [String]
    -- ^ rendered candidate groups (best first), operational notes
  | SynthRefuted Bool
    -- ^ no inhabitant; 'True' means the verdict is sound (complete
    -- translation, no structure-hiding atoms)
  | SynthNoTerm [String]
    -- ^ no candidate and no logical claim, with notes

-- | How many engine candidates take part in the size ranking.  The
-- backend verification round-trip is the cost center, not rendering, so
-- this can comfortably exceed the number of candidates ever shown.
-- | How many engine candidates are collected and take part in the size
-- ranking.  Djinn's sorted mode computes the whole collection before
-- returning, so this bounds real work; the default of 200 buys nothing
-- when at most a handful are ever displayed.  Reaching it truncates the
-- batch, which carries no negative evidence, so refutations - which
-- come from an exhausted search rather than a full collection - stay
-- sound.
candidateWindow :: Int
candidateWindow = 60

-- | Drive an outcome's evaluation far enough that the whole search has
-- run: the verdict itself, plus the first @n@ candidate groups.  The
-- caller runs this under a wall-clock guard - the engine is pure and
-- lazy, so without forcing, the search would instead happen later,
-- outside the guard.
forceOutcome :: Int -> Either String SynthOutcome -> Int
forceOutcome n outcome = case outcome of
  Left err -> length err
  Right (SynthCandidates groups notes) ->
    sum (map (sum . map length) (take n groups)) + noteSize notes
  Right (SynthRefuted sound) -> if sound then 1 else 0
  Right (SynthNoTerm notes) -> noteSize notes
 where
  noteSize = sum . map length

-- | Run the in-process Djinn (LJT) search on a translated goal.
synthesize :: Frag -> Either String SynthOutcome
synthesize frag = do
  session <- viaDiagnostic standardDjinnSession
  targetName <- viaShow (mkIdentifier "leantSynth")
  target <- viaShow (mkDefinitionName targetName)
  goal <- fragToDjinn frag
  let query = QueryRequest
        { requestTarget = target
        , requestGoal = goal
        , requestContexts = []
        , requestOptions = defaultQueryOptions
            { optionAlternatives = True
            , optionCutoff = candidateWindow
            }
        }
  request <- viaDiagnostic (mkDjinnRequest query)
  result <- viaDiagnostic (runDjinnQuery session request)
  let batch = resultSearch result
      notes = progressNotes (batchProgress batch)
      -- Djinn ranks by unused-binder fraction, which happily puts a
      -- redundantly re-cased monster ahead of the obvious term.  Prefer
      -- smaller terms, keeping the engine's order as the tie-break, over
      -- a bounded prefix (the batch is terminal but can be long).
      rendered =
        [ (expressionSize expr, group)
        | candidate <- take candidateWindow (batchCandidates batch)
        , let expr = functionClauseExpression (candidateOutput candidate)
        , Right group <- [renderLeanTerm frag expr]
        ]
      terms = map snd (sortOn fst rendered)
  pure $ case resultEvidence result of
    ValidatedCandidates -> SynthCandidates terms notes
    ProvedUninhabitable -> SynthRefuted (null (fragUnsafeAtoms frag))
    RequiresTargetReference -> SynthNoTerm
      ("only a recursive reference to the definition itself would inhabit \
       \this type" : notes)
    NoEvidence -> SynthNoTerm notes
 where
  viaDiagnostic = either (Left . renderDiagnostic) Right
  viaShow :: Show e => Either e a -> Either String a
  viaShow = either (Left . show) Right

progressNotes :: Progress -> [String]
progressNotes progress = case progress of
  Completed Finished -> []
  Completed (Truncated reasons) ->
    ["search truncated: " ++ show reasons]
  Continuing -> ["search reported more batches to come"]

-- Fragment -> Djinn type ----------------------------------------------------
--
-- Opaque variables and atoms both become Djinn type variables; atoms are
-- keyed by their pretty-printed spelling so alpha-equal occurrences share
-- one variable (transportable, never analyzed).  Nested quantifiers are
-- passed structurally as 'ForallType'; Djex carries them as alpha-aware
-- atoms and applies its bounded rank-N rules.

fragToDjinn :: Frag -> Either String (Type String)
fragToDjinn frag0 = do
  eitherC <- name (mkIdentifier "Either")
  voidC <- name (mkIdentifier "Void")
  unitC <- name (tupleName Boxed 0)
  let go table n frag = case frag of
        FArr a b -> binary FunctionType table n a b
        FProd a b ->
          binary (\x y -> TupleType Boxed [x, y]) table n a b
        FSum a b ->
          binary
            (\x y -> TypeApplication
              (TypeApplication (TypeConstructor eitherC) x) y)
            table n a b
        FTop -> Right (TypeConstructor unitC, table, n)
        FBot -> Right (TypeConstructor voidC, table, n)
        FVar v ->
          let (v', table', n') = variable table n ("v:" ++ v)
          in Right (TypeVariable v', table', n')
        FAtom _ key ->
          let (v', table', n') = variable table n ("a:" ++ key)
          in Right (TypeVariable v', table', n')
        FAll _ binder body -> do
          let (v, table1, n1) = variable table n ("v:" ++ binder)
          (body', table2, n2) <- go table1 n1 body
          Right (ForallType [v] [] body', table2, n2)
        FDepth -> Left "internal: depth marker survived refusal check"
      binary ctor table n a b = do
        (a', table1, n1) <- go table n a
        (b', table2, n2) <- go table1 n1 b
        Right (ctor a' b', table2, n2)
      variable table n key = case Map.lookup key table of
        Just v -> (v, table, n)
        Nothing ->
          let v = "v" ++ show (n :: Int)
          in (v, Map.insert key v table, n + 1)
  (djinnType, _, _) <- go Map.empty 0 frag0
  Right djinnType
 where
  name :: Show e => Either e a -> Either String a
  name = either (Left . show) Right
