(**
  Native direct truth inputs with their exact closure remainder.

  The native truth package already supplies the two deep ternary predicates
  and the literal equations identifying the direct context/conclusion leaves
  with their selected applications.  Ordinary direct-body closure turns those
  facts into substitution identity at every carrier-valued depth; formula-
  bound and universal-closure totality then choose the nonstandard closure
  count and sealed induction axiom.

  We use the quoted zero term as the closure compiler's protected
  replacement.  Its all-zero assignment columns are represented term syntax,
  so this choice adds no external syntax premise.  Most importantly, the
  combined package below retains the *same* dependent selectors and structural
  input value from the native trace while adjoining the exact remainder.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedAssignmentTotality
  RawCodedTermEvaluationRealization
  RawCodedProofAtomicAdequacyStandard
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicContextTruthSelector
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs
  RawCodedRestrictedPADerivationSoundnessDirectOrdinaryClosure
  RawCodedRestrictedPADerivationSoundnessDirectOrdinaryClosureRemainder.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeCoherentDirectTruthInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrdinaryClosure.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrdinaryClosureRemainder.

(** A fixed closed replacement keeps the public native package free of an
    arbitrary term-syntax side condition. *)
Definition rawCoqRestrictedPADirectClosureReplacement
    (M : RawPAModel) : M :=
  rawQuotedTermCode M tZero.

Arguments rawCoqRestrictedPADirectClosureReplacement M : clear implicits.

Lemma raw_coqRestrictedPADirectClosureReplacement_realizable : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawTermSyntaxRealizable M
    (rawCoqRestrictedPADirectClosureReplacement M)
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA.
  unfold rawCoqRestrictedPADirectClosureReplacement.
  apply (raw_quotedTerm_syntax_realizable_of_assignment
    M hPA tZero (raw_zero M) (raw_zero M)).
  exact (raw_codedZeroAssignment_defined_all M hPA
    (raw_succ M (rawQuotedTermCode M tZero))).
Qed.

(** The small reusable bridge: exact leaf equations plus deep ternary
    closure produce the complete induction-closure remainder for the same
    direct structural input. *)
Theorem
    raw_coqRestrictedPADirectClosureRemainder_exists_of_ternary_leaf_equations
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      contextPredicate conclusionPredicate
      (contextApplicationSelector :
        RawCodedTernaryApplicationSelector M contextPredicate)
      (conclusionApplicationSelector :
        RawCodedTernaryApplicationSelector M conclusionPredicate)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  inputs =
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth ->
  RawCodedTernaryPredicateDeepClosed M contextPredicate ->
  RawCodedTernaryPredicateDeepClosed M conclusionPredicate ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAContextTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput contextApplicationSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)) ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput conclusionApplicationSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  exists closureCount axiom : M,
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs (rawCoqRestrictedPADirectClosureReplacement M)
      axiom closureCount.
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    contextPredicate conclusionPredicate
    contextApplicationSelector conclusionApplicationSelector
    inputs hinputs hcontextDeep hconclusionDeep
    hcontextLeaf hconclusionLeaf.
  subst inputs.
  apply
    (raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_exists_of_ordinary_identity_total
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      (rawCoqRestrictedPADirectClosureReplacement M)).
  exact
    (raw_coqRestrictedPADerivationSoundnessCarrierStrongPrefixBodyDirect_substitution_identity_of_ternary_leaf_equations
      M hPA parameters contextTruth conclusionTruth
      contextPredicate conclusionPredicate
      contextApplicationSelector conclusionApplicationSelector
      (rawCoqRestrictedPADirectClosureReplacement M)
      (raw_zero M) (raw_zero M)
      (raw_coqRestrictedPADirectClosureReplacement_realizable M hPA)
      hcontextDeep hconclusionDeep hcontextLeaf hconclusionLeaf).
Qed.

(** The original native package, refined by closure data for its very same
    [inputs].  The ordering of all earlier fields is intentionally unchanged,
    making comparison with [RawCoqRestrictedPANativeDirectTruthInputsAt]
    mechanical; the remainder is the final conjunct. *)
Definition RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence : M) : Prop :=
  exists nextGlobalSigma nextGlobalPi : M,
  exists sigmaApplicationSelector :
    RawCodedTernaryApplicationSelector M nextGlobalSigma,
  exists contextApplicationSelector :
    RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector),
  exists contextTruth conclusionTruth :
    RawCoqRestrictedPATruthDirectSelector M parameters,
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
  exists closureCount axiom : M,
    RawDynamicTruthPairedGlobalSuccessorAt M
      currentGlobalSigma currentGlobalPi
      (raw_succ M predecessorLevel) nextGlobalSigma nextGlobalPi /\
    RawCodedTernaryPredicateDeepClosed M nextGlobalSigma /\
    RawCodedTernaryPredicateDeepClosed M
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector) /\
    inputs =
      rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth /\
    (forall lower upper context assignmentCode assignmentStep,
      rawCoqRestrictedPATruthDirectOutput contextTruth
        lower upper context assignmentCode assignmentStep =
      rawTernaryApplicationOutput contextApplicationSelector
        assignmentStep assignmentCode context) /\
    (forall lower upper conclusion assignmentCode assignmentStep,
      rawCoqRestrictedPATruthDirectOutput conclusionTruth
        lower upper conclusion assignmentCode assignmentStep =
      rawTernaryApplicationOutput sigmaApplicationSelector
        conclusion assignmentCode assignmentStep) /\
    (forall first second third fourth fifth,
      rawDirectTemplateFormula inputs
        (tfOpaque coqRestrictedPAContextTruthPredicateName
          [first; second; third; fourth; fifth]) =
      rawTernaryApplicationOutput contextApplicationSelector
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fifth)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fourth)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters third)) /\
    (forall first second third fourth fifth,
      rawDirectTemplateFormula inputs
        (tfOpaque coqRestrictedPAConclusionTruthPredicateName
          [first; second; third; fourth; fifth]) =
      rawTernaryApplicationOutput sigmaApplicationSelector
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters third)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fourth)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fifth)) /\
    rawTernaryApplicationOutput sigmaApplicationSelector
      (rawQuotedTermCode M (tVar 0))
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero) = nextSigmaEvidence /\
    (forall lower upper,
      rawCoqRestrictedPATruthDirectOutput conclusionTruth
        lower upper
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M tZero)
        (rawQuotedTermCode M tZero) = nextSigmaEvidence) /\
    RawCodedTernaryApplication M nextGlobalSigma
      (rawQuotedTermCode M (tVar 0))
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero)
      nextSigmaEvidence /\
    RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder
      M inputs (rawCoqRestrictedPADirectClosureReplacement M)
      axiom closureCount.

Arguments RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt
  M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
  nextSigmaEvidence : clear implicits.

Theorem raw_coqRestrictedPANativeDirectTruthInputsWithClosureAt_of_inputs :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs.
  unfold RawCoqRestrictedPANativeDirectTruthInputsAt in hinputs.
  destruct hinputs as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & contextTruth & conclusionTruth & inputs &
     hsuccessor & hsigmaDeep & hcontextDeep & hinputs &
     hcontextOutput & hconclusionOutput & hcontextLeaf & hconclusionLeaf &
     hselectorNative & hconclusionNative & happlication).
  destruct
    (raw_coqRestrictedPADirectClosureRemainder_exists_of_ternary_leaf_equations
      M hPA parameters contextTruth conclusionTruth
      (rawDynamicContextAllSigmaCode sigmaApplicationSelector)
      nextGlobalSigma contextApplicationSelector sigmaApplicationSelector
      inputs hinputs hcontextDeep hsigmaDeep hcontextLeaf hconclusionLeaf)
    as (closureCount & axiom & hremainder).
  exists nextGlobalSigma, nextGlobalPi,
    sigmaApplicationSelector, contextApplicationSelector,
    contextTruth, conclusionTruth, inputs, closureCount, axiom.
  split; [exact hsuccessor |].
  split; [exact hsigmaDeep |].
  split; [exact hcontextDeep |].
  split; [exact hinputs |].
  split; [exact hcontextOutput |].
  split; [exact hconclusionOutput |].
  split; [exact hcontextLeaf |].
  split; [exact hconclusionLeaf |].
  split; [exact hselectorNative |].
  split; [exact hconclusionNative |].
  split; [exact happlication |].
  exact hremainder.
Qed.

(** Finally retain the stage equations tying the displayed lower/upper
    parameters to this same native trace. *)
Definition RawCoqRestrictedPANativeCoherentDirectTruthInputsWithClosureAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence : M) : Prop :=
  exists parameters : RawCodedTemplateNumeralParameters M,
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessLowerLevelParameterName =
      raw_succ M predecessorLevel /\
    rawNumeralTemplateParameterBound parameters
      coqRestrictedPASoundnessUpperLevelParameterName =
      raw_succ M (raw_succ M predecessorLevel) /\
    RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt
      M hPA parameters currentGlobalSigma currentGlobalPi
      predecessorLevel nextSigmaEvidence.

Arguments RawCoqRestrictedPANativeCoherentDirectTruthInputsWithClosureAt
  M hPA currentGlobalSigma currentGlobalPi predecessorLevel
  nextSigmaEvidence : clear implicits.

Theorem
    raw_coqRestrictedPANativeCoherentDirectTruthInputsWithClosureAt_of_trace :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence,
  RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence ->
  RawCoqRestrictedPANativeCoherentDirectTruthInputsWithClosureAt M hPA
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence.
Proof.
  intros M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence htrace.
  destruct
    (raw_coqRestrictedPANativeCoherentDirectTruthInputsAt_of_trace
      M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence htrace)
    as (parameters & hlower & hupper & hinputs).
  exists parameters. split; [exact hlower |].
  split; [exact hupper |].
  exact
    (raw_coqRestrictedPANativeDirectTruthInputsWithClosureAt_of_inputs
      M hPA parameters currentGlobalSigma currentGlobalPi
      predecessorLevel nextSigmaEvidence hinputs).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
