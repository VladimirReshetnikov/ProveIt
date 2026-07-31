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
--
-- Phase 2: expanded inductive occurrences ('FInd') become Djinn @data@
-- declarations -- constructors as right-rules, case analysis as
-- left-rules, exactly how Djinn admits Haskell datatypes.  Each distinct
-- occurrence key (one per alpha-normalized instantiation) is declared
-- once, parameterized over the goal variables its fields mention, and
-- the goal references the declared constructor applied to those
-- variables.  The engine-side constructor names are fresh; the mapping
-- back to the Lean spellings rides along to the renderer.
module Leant.Synth.Engine
  ( SynthEngine (..)
  , SynthOutcome (..)
  , parseSynthEngine
  , synthEngineName
  , synthesize
  , forceOutcome
  , candidateWindow
  ) where

import Data.Foldable (toList)
import Data.List (intercalate, nub, sortOn)
import qualified Data.Map.Strict as Map
import Data.Void (Void)

import Language.Haskell.Djex
  ( QueryEvidence (..)
  , QueryOptions (..)
  , QueryRequest (..)
  , Boxity (Boxed)
  , Completion (..)
  , DataConstructor (..)
  , Declaration (DataTypeDeclaration)
  , Diagnostic
  , ExferenceOptions (..)
  , Expression
  , Name
  , Progress (..)
  , Selection (..)
  , SelectionMode (SelectAll)
  , TruncationReason (..)
  , Type (..)
  , TypeParameter (..)
  , Variable (FlexibleVariable)
  , applyTypeArguments
  , batchCandidates
  , batchProgress
  , candidateOutput
  , declarationTypeVariables
  , defaultExferenceOptions
  , defaultQueryOptions
  , djinnSessionEnvironment
  , environmentDeclarations
  , expressionSize
  , functionClauseExpression
  , mapDeclarationTypeVariables
  , mkDefinitionName
  , mkDjinnRequest
  , mkDjinnSession
  , mkEnvironment
  , mkExferenceRequest
  , mkExferenceSession
  , mkIdentifier
  , renderDiagnostic
  , resultEvidence
  , resultSearch
  , runDjinnQuery
  , runExferenceQuery
  , selectQueryResults
  , standardDjinnSession
  , tupleName
  )

import Leant.Synth.Fragment (Frag (..), fragUnsafeAtoms)
import Leant.Synth.Render (CtorInfo (..), CtorMap, renderLeanTerm)

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

-- | Which synthesis engine(s) a query runs (proposal F of
-- SYNTHESIS_PROPOSAL.md \167 7).  Djinn is the complete, terminating LJT
-- search with refutation verdicts; Exference is a ranked heuristic
-- search under explicit budgets, with no negative evidence.
data SynthEngine = EngineDjinn | EngineExference | EngineBoth
  deriving (Eq, Show)

parseSynthEngine :: String -> Maybe SynthEngine
parseSynthEngine value = case value of
  "djinn" -> Just EngineDjinn
  "exference" -> Just EngineExference
  "both" -> Just EngineBoth
  _ -> Nothing

synthEngineName :: SynthEngine -> String
synthEngineName engine = case engine of
  EngineDjinn -> "djinn"
  EngineExference -> "exference"
  EngineBoth -> "both"

-- | Run the selected in-process search on a translated goal.  The
-- step budget applies to Exference only (Djinn's complete search needs
-- no budget beyond the candidate window).
synthesize :: SynthEngine -> Int -> Frag -> Either String SynthOutcome
synthesize engine steps frag = do
  (goal0, decls, ctorMap, premises) <- fragToDjinn frag
  -- constructor premises of recursive inductives enter as goal
  -- antecedents (same scope as the goal's variables - a top-level
  -- declaration would generalize them); the renderer strips the
  -- matching binders and substitutes the Lean constructor names
  let goal = foldr (\(_, t) acc -> FunctionType t acc) goal0 premises
      premiseNames = map fst premises
      render expr = renderLeanTerm ctorMap premiseNames frag expr
  case engine of
    EngineDjinn -> djinnRun frag render goal decls
    EngineExference -> exferenceRun steps render goal decls
    EngineBoth -> do
      djinn <- djinnRun frag render goal decls
      exference <- exferenceRun steps render goal decls
      pure (mergeOutcomes djinn exference)

-- | The complete LJT search: candidates, or a refutation whose
-- soundness depends on the translation having hidden nothing.
djinnRun
  :: Frag
  -> (Expression String -> Either String [String])
  -> Type String
  -> [DjinnDecl]
  -> Either String SynthOutcome
djinnRun frag render goal decls = do
  standard <- viaDiagnostic standardDjinnSession
  targetName <- viaShow (mkIdentifier "leantSynth")
  target <- viaShow (mkDefinitionName targetName)
  session <-
    if null decls
      then Right standard
      else do
        environment <- viaShow $ mkEnvironment
          (environmentDeclarations (djinnSessionEnvironment standard)
           ++ decls)
        viaDiagnostic (mkDjinnSession environment)
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
        , Right group <- [render expr]
        ]
      terms = map snd (sortOn fst rendered)
  pure $ case resultEvidence result of
    ValidatedCandidates -> SynthCandidates terms notes
    ProvedUninhabitable -> SynthRefuted (null (fragUnsafeAtoms frag))
    RequiresTargetReference -> SynthNoTerm
      ("only a recursive reference to the definition itself would inhabit \
       \this type" : notes)
    NoEvidence -> SynthNoTerm notes

-- | The ranked heuristic search: the same shared environment and goal,
-- converted to Exference's integer variable domain.  Candidates keep
-- Exference's own ranking; there is never negative evidence.
exferenceRun
  :: Int
  -> (Expression String -> Either String [String])
  -> Type String
  -> [DjinnDecl]
  -> Either String SynthOutcome
exferenceRun steps render goal decls = do
  standard <- viaDiagnostic standardDjinnSession
  let allDecls =
        environmentDeclarations (djinnSessionEnvironment standard)
          ++ decls
      names = nub
        (concatMap declarationTypeVariables allDecls ++ toList goal)
      table = Map.fromList (zip names [0 :: Int ..])
      convert v = FlexibleVariable (table Map.! v)
  environment <- viaShow
    (mkEnvironment (map (mapDeclarationTypeVariables convert) allDecls))
  session <- viaDiagnostic (mkExferenceSession environment)
  targetName <- viaShow (mkIdentifier "leantSynth")
  target <- viaShow (mkDefinitionName targetName)
  let query = QueryRequest
        { requestTarget = target
        , requestGoal = fmap convert goal
        , requestContexts = []
        , requestOptions = defaultExferenceOptions
            { exferenceMaximumSteps = steps
              -- the queue is the memory hog; a modest bound keeps the
              -- search interactive on small machines, reported honestly
              -- as pruning
            , exferenceMaximumQueueSize = Just 1024
            }
        }
  request <- viaDiagnostic (mkExferenceRequest query)
  results <- viaDiagnostic (runExferenceQuery session request)
  let selection =
        selectQueryResults SelectAll (const (0 :: Int)) (const True) results
      groups = nub
        [ group
        | candidate <- take candidateWindow (selectionCandidates selection)
        , let expr = fmap (("x" ++) . show)
                (functionClauseExpression (candidateOutput candidate))
        , Right group <- [render expr]
        ]
      notes = maybe [] progressNotes (selectionProgress selection)
  pure $ if null groups
    then SynthNoTerm notes
    else SynthCandidates groups notes

-- | Both engines on one goal: Djinn's candidates first (they carry the
-- smallest-term ranking), Exference's new ones after, and negative
-- verdicts only when neither engine produced a candidate - a refutation
-- stays Djinn's alone.
mergeOutcomes :: SynthOutcome -> SynthOutcome -> SynthOutcome
mergeOutcomes djinn exference = case (djinn, exference) of
  (SynthCandidates a na, SynthCandidates b nb) ->
    SynthCandidates (a ++ filter (`notElem` a) b) (na ++ tag nb)
  (SynthCandidates a na, other) ->
    SynthCandidates a (na ++ tag (notesOf other))
  (other, SynthCandidates b nb) ->
    SynthCandidates b (notesOf other ++ tag nb)
  (SynthRefuted sound, _) -> SynthRefuted sound
  (SynthNoTerm na, other) -> SynthNoTerm (na ++ tag (notesOf other))
 where
  tag = map ("exference: " ++)
  notesOf outcome = case outcome of
    SynthCandidates _ notes -> notes
    SynthNoTerm notes -> notes
    SynthRefuted _ -> []

viaDiagnostic :: Either Diagnostic a -> Either String a
viaDiagnostic = either (Left . renderDiagnostic) Right

viaShow :: Show e => Either e a -> Either String a
viaShow = either (Left . show) Right

progressNotes :: Progress -> [String]
progressNotes progress = case progress of
  Completed Finished -> []
  Completed (Truncated reasons) ->
    [ "search truncated: "
      ++ intercalate ", " (map reasonText (nub (toList reasons))) ]
  Continuing -> ["search reported more batches to come"]
 where
  reasonText reason = case reason of
    StepLimitReached -> "step limit reached"
    ChoicePointLimitReached -> "choice-point limit reached"
    CandidateLimitReached ->
      "candidate limit reached (" ++ show candidateWindow ++ ")"
    IdentifierSpaceExhausted -> "identifier space exhausted"
    QueueLimitPruned n -> "queue limit pruned " ++ show n
    DepthLimitPruned n -> "depth limit pruned " ++ show n

-- Fragment -> Djinn type ----------------------------------------------------
--
-- Opaque variables and atoms both become Djinn type variables; atoms are
-- keyed by their pretty-printed spelling so alpha-equal occurrences share
-- one variable (transportable, never analyzed).  Nested quantifiers are
-- passed structurally as 'ForallType'; Djex carries them as alpha-aware
-- atoms and applies its bounded rank-N rules.  Expanded inductive
-- occurrences become fresh @data@ declarations, one per display key,
-- collected in dependency order (fields are translated before the
-- declaration that contains them).

-- | The neutral declaration shape sealed into a 'DjinnSession' (the
-- @Environment String Void ()@ element type of 'DjinnEnvironment').
type DjinnDecl = Declaration String Void ()

data TransState = TransState
  { tsTable :: Map.Map String String
    -- ^ goal variable\/atom key -> engine type variable
  , tsNext :: Int
  , tsInds :: Map.Map String (Type String)
    -- ^ inductive display key -> its occurrence type
  , tsDecls :: [DjinnDecl]
    -- ^ new data declarations, dependency order
  , tsIndNext :: Int
  , tsCtorMap :: CtorMap
    -- ^ engine constructor spelling -> (Lean name, field fragments)
  , tsRecs :: Map.Map String ()
    -- ^ recursive-inductive keys whose constructor premises are
    -- already registered
  , tsPrems :: [(String, Type String)]
    -- ^ constructor premises (Lean name, engine type), in order
  }

newtype Trans a = Trans
  { runTrans :: TransState -> Either String (a, TransState) }

instance Functor Trans where
  fmap f (Trans g) = Trans $ \s -> do
    (a, s') <- g s
    Right (f a, s')

instance Applicative Trans where
  pure a = Trans (\s -> Right (a, s))
  Trans f <*> Trans g = Trans $ \s -> do
    (h, s1) <- f s
    (a, s2) <- g s1
    Right (h a, s2)

instance Monad Trans where
  Trans g >>= k = Trans $ \s -> do
    (a, s1) <- g s
    runTrans (k a) s1

failT :: String -> Trans a
failT msg = Trans (\_ -> Left msg)

getsT :: (TransState -> a) -> Trans a
getsT f = Trans (\s -> Right (f s, s))

modifyT :: (TransState -> TransState) -> Trans ()
modifyT f = Trans (\s -> Right ((), f s))

nameT :: String -> Trans Name
nameT spelling = Trans $ \s ->
  case mkIdentifier spelling of
    Left err -> Left (show err)
    Right name -> Right (name, s)

variable :: String -> Trans String
variable key = do
  table <- getsT tsTable
  case Map.lookup key table of
    Just v -> pure v
    Nothing -> do
      n <- getsT tsNext
      let v = "v" ++ show n
      modifyT (\s -> s { tsTable = Map.insert key v (tsTable s)
                       , tsNext = n + 1 })
      pure v

fragToDjinn
  :: Frag
  -> Either String
      (Type String, [DjinnDecl], CtorMap, [(String, Type String)])
fragToDjinn frag0 = do
  eitherC <- viaShow (mkIdentifier "Either")
  voidC <- viaShow (mkIdentifier "Void")
  unitC <- viaShow (tupleName Boxed 0)
  let go frag = case frag of
        FArr a b -> FunctionType <$> go a <*> go b
        FProd a b -> (\x y -> TupleType Boxed [x, y]) <$> go a <*> go b
        FSum a b ->
          (\x y -> TypeApplication
            (TypeApplication (TypeConstructor eitherC) x) y)
          <$> go a <*> go b
        FTop -> pure (TypeConstructor unitC)
        FBot -> pure (TypeConstructor voidC)
        FVar v -> TypeVariable <$> variable ("v:" ++ v)
        FAtom _ key -> TypeVariable <$> variable ("a:" ++ key)
        FAll _ binder body -> do
          v <- variable ("v:" ++ binder)
          body' <- go body
          pure (ForallType [v] [] body')
        FInd key ctors -> indOccurrence key ctors
        FRec key ctors -> recOccurrence key ctors
        FDepth -> failT "internal: depth marker survived refusal check"

      -- One declaration per display key: translate the fields first
      -- (declaring any nested inductives before this one), parameterize
      -- over the type variables the translated fields mention, cache the
      -- applied occurrence.
      indOccurrence key ctors = do
        existing <- getsT (Map.lookup key . tsInds)
        case existing of
          Just occurrence -> pure occurrence
          Nothing -> do
            translated <- mapM
              (\(leanName, fields) -> do
                fieldTypes <- mapM go fields
                pure (leanName, fields, fieldTypes))
              ctors
            index <- getsT tsIndNext
            modifyT (\s -> s { tsIndNext = index + 1 })
            typeName <- nameT ("LeantData" ++ show index)
            let params = nub
                  [ v
                  | (_, _, fieldTypes) <- translated
                  , fieldType <- fieldTypes
                  , v <- toList fieldType
                  ]
            let sole = length translated == 1
            constructors <- mapM
              (\(j, (leanName, fields, fieldTypes)) -> do
                let spelling = "LeantC" ++ show index ++ "_" ++ show j
                cname <- nameT spelling
                modifyT (\s -> s { tsCtorMap = Map.insert spelling
                    (CtorInfo leanName fields sole) (tsCtorMap s) })
                pure (DataConstructor () cname fieldTypes))
              (zip [0 :: Int ..] translated)
            -- kinds stay implicit: Djinn's lowering rejects explicit
            -- parameter kinds and infers @*@ itself
            let decl = DataTypeDeclaration () typeName
                  [ TypeParameter p Nothing | p <- params ]
                  constructors
                occurrence = applyTypeArguments (TypeConstructor typeName)
                  (map TypeVariable params)
            modifyT (\s -> s { tsInds = Map.insert key occurrence (tsInds s)
                             , tsDecls = tsDecls s ++ [decl] })
            pure occurrence

      -- A recursive inductive stays an opaque atom (sharing the
      -- variable any blocked field occurrence produced), but its
      -- constructors become premise types the caller prepends to the
      -- goal as antecedents - introduction rules without elimination.
      recOccurrence key ctors = do
        occurrence <- TypeVariable <$> variable ("a:" ++ key)
        registered <- getsT (Map.member key . tsRecs)
        if registered
          then pure occurrence
          else do
            modifyT (\s -> s { tsRecs = Map.insert key () (tsRecs s) })
            mapM_
              (\(leanName, fields) -> do
                fieldTypes <- mapM go fields
                let premise = foldr FunctionType occurrence fieldTypes
                modifyT (\s -> s
                  { tsPrems = tsPrems s ++ [(leanName, premise)] }))
              ctors
            pure occurrence

  (goal, finalState) <- runTrans (go frag0) TransState
    { tsTable = Map.empty
    , tsNext = 0
    , tsInds = Map.empty
    , tsDecls = []
    , tsIndNext = 0
    , tsCtorMap = Map.empty
    , tsRecs = Map.empty
    , tsPrems = []
    }
  Right (goal, tsDecls finalState, tsCtorMap finalState
        , tsPrems finalState)
