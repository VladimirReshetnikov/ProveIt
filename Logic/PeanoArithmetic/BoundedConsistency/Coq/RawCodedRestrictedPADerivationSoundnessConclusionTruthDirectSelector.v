(**
  The concrete conclusion-truth selector for derivation soundness.

  The direct soundness template presents conclusion truth as an opaque
  five-argument family

      (lower, upper, conclusion, assignmentCode, assignmentStep).

  At one fixed dynamic-truth stage, the first two arguments have already
  selected the graph-produced global Sigma predicate.  The resulting formula
  is therefore ternary application of that *same* predicate to the final
  three arguments.  This file packages that application as the exact direct
  selector expected by
  [RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs].

  There are two points at which it would be easy to overstate the result.

  - The global Sigma code is never decoded into a metatheoretic formula.
    Its represented deep-closure certificate supplies shift and opening
    commutation at arbitrary carrier cutoffs.
  - The native PA-axiom trace already contains an application of the
    graph-selected successor Sigma code.  Functionality identifies that
    relational output with the selector output; no semantic completeness or
    standard-model principle is used.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTermOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTernaryPredicateDeepClosure
  RawCodedTernaryPredicateDeepClosureShiftInterchange
  RawCodedTernaryPredicateDeepClosureOpeningCommuting
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthGlobalSuccessorDeepClosure
  RawCodedDynamicTruthPairedSuccessorLocalDeepClosure
  RawCodedDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitGraph
  RawCodedDynamicTruthPairedGlobalOrbitFunctionality
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicTruthNativeAxiomApplicationTernaryAlignment
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessConclusionTruthDirectSelector.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedTernaryPredicateDeepClosureShiftInterchange.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningCommuting.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
Import PABoundedRawCodedDynamicTruthPairedSuccessorLocalDeepClosure.
Import
  PABoundedRawCodedDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalOrbitFunctionality.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAxiomApplicationTernaryAlignment.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

(** ------------------------------------------------------------------
    Lift one deeply closed ternary predicate selector to the exact direct
    five-argument conclusion interface.

    The [lower] and [upper] inputs are intentionally ignored here: the
    [predicate] argument is already the successor predicate selected by that
    particular graph edge.  Retaining them in the function type is essential,
    however, because it preserves the literal arity and ordering of the
    derivation-soundness template. *)

Definition rawCoqRestrictedPAConclusionTruthDirectSelector_of_ternary
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (predicate : M)
    (applicationSelector :
      RawCodedTernaryApplicationSelector M predicate)
    (hdeep : RawCodedTernaryPredicateDeepClosed M predicate)
    : RawCoqRestrictedPATruthDirectSelector M parameters.
Proof.
  refine
    {| rawCoqRestrictedPATruthDirectOutput :=
         fun _lower _upper conclusion assignmentCode assignmentStep =>
           rawTernaryApplicationOutput applicationSelector
             conclusion assignmentCode assignmentStep;
       rawCoqRestrictedPATruthDirectShiftAt := _;
       rawCoqRestrictedPATruthDirectOpeningAt := _ |}.
  - intros depth first second third fourth fifth.
    apply (rawTernaryApplicationSelector_shift_commuting_on_syntax
      M hPA predicate applicationSelector
      (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
        M hPA predicate hdeep)).
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift;
        exact hPA.
  - intros depth replacement first second third fourth fifth.
    apply
      (rawTernaryApplicationSelector_opening_commuting_on_syntax_of_deepClosed_concrete
        M hPA predicate applicationSelector hdeep).
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening;
        exact hPA.
    + apply
        rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening;
        exact hPA.
Defined.

Arguments rawCoqRestrictedPAConclusionTruthDirectSelector_of_ternary
  M _ _ predicate applicationSelector _ : clear implicits.

(** The output equation makes the five-argument order auditable without
    unfolding either proof field of the direct selector record. *)
Lemma rawCoqRestrictedPAConclusionTruthDirectSelector_output : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    predicate applicationSelector hdeep
    lower upper conclusion assignmentCode assignmentStep,
  rawCoqRestrictedPATruthDirectOutput
    (rawCoqRestrictedPAConclusionTruthDirectSelector_of_ternary
      M hPA parameters predicate applicationSelector hdeep)
    lower upper conclusion assignmentCode assignmentStep =
  rawTernaryApplicationOutput applicationSelector
    conclusion assignmentCode assignmentStep.
Proof. reflexivity. Qed.

(** On any honest three arguments, the direct output is the unique output of
    the represented ternary-application relation.  This is the precise raw
    relational meaning supplied here; it is deliberately not restated as
    metatheoretic satisfaction of an arbitrarily decoded formula. *)
Theorem rawCoqRestrictedPAConclusionTruthDirectSelector_output_unique :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    predicate applicationSelector hdeep
    lower upper conclusion assignmentCode assignmentStep output,
  RawCodedTermSyntax M conclusion ->
  RawCodedTermSyntax M assignmentCode ->
  RawCodedTermSyntax M assignmentStep ->
  RawCodedTernaryApplication M predicate
    conclusion assignmentCode assignmentStep output ->
  rawCoqRestrictedPATruthDirectOutput
    (rawCoqRestrictedPAConclusionTruthDirectSelector_of_ternary
      M hPA parameters predicate applicationSelector hdeep)
    lower upper conclusion assignmentCode assignmentStep = output.
Proof.
  intros M hPA parameters predicate applicationSelector hdeep
    lower upper conclusion assignmentCode assignmentStep output
    hconclusion hassignmentCode hassignmentStep happlication.
  rewrite rawCoqRestrictedPAConclusionTruthDirectSelector_output.
  exact (rawTernaryApplicationOutput_unique M hPA
    predicate applicationSelector
    conclusion assignmentCode assignmentStep output
    hconclusion hassignmentCode hassignmentStep happlication).
Qed.

(** Substitution into the named soundness template now visibly has the exact
    order [(conclusion, assignmentCode, assignmentStep)] after the two
    level-code parameters.  This statement is useful to clients compiling
    the strong-step formula, because it avoids unfolding the selector record
    or either direct structural proof field. *)
Theorem
    rawCoqRestrictedPADerivationSoundnessConclusionTruthTemplate_ternary_view
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      predicate applicationSelector hdeep
      (contextTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters),
    let conclusionTruth :=
      rawCoqRestrictedPAConclusionTruthDirectSelector_of_ternary
        M hPA parameters predicate applicationSelector hdeep in
    let inputs :=
      rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth in
    rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessConclusionTruthTemplate =
    rawTernaryApplicationOutput applicationSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
        (ttVar 2))
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
        (ttVar 1))
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
        (ttVar 0)).
Proof.
  intros M hPA parameters predicate applicationSelector hdeep contextTruth.
  cbn zeta.
  rewrite
    (rawCoqRestrictedPADerivationSoundnessConclusionTruthTemplate_view
      M hPA parameters contextTruth
      (rawCoqRestrictedPAConclusionTruthDirectSelector_of_ternary
        M hPA parameters predicate applicationSelector hdeep)).
  apply rawCoqRestrictedPAConclusionTruthDirectSelector_output.
Qed.

(** Ordinary quoted terms are in the honest selector domain.  We derive
    this using a zero-shift trace so that the statement does not depend on a
    separate decoder or on standard-model semantics. *)
Lemma raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawCodedTermSyntax M (rawQuotedTermCode M input).
Proof.
  intros M hPA input.
  pose proof (raw_codedTermShift_standard M hPA 0 0 input) as hshift.
  change (RawCodedTermShift M
      (rawNumeralValue M 0) (rawNumeralValue M 0)
      (rawQuotedTermCode M input)
      (rawQuotedTermCode M (standardTermShift 0 0 input))) in hshift.
  rewrite standardTermShift_zero_zero in hshift.
  exact (raw_codedTermShift_target_syntax M hPA
    (rawNumeralValue M 0) (rawNumeralValue M 0)
    (rawQuotedTermCode M input) (rawQuotedTermCode M input) hshift).
Qed.

(** ------------------------------------------------------------------
    Extract the selector from the native axiom trace.

    The trace supplies an adequate current orbit, not a deep-closed one.
    We independently run the represented deep-closed orbit induction at the
    same (possibly nonstandard) carrier level.  Orbit functionality identifies
    its pair with the trace pair.  Deep closure then propagates across the
    *actual successor edge stored in the trace*, ensuring that the predicate
    used below is literally the trace's [nextGlobalSigma]. *)

Theorem
    raw_coqRestrictedPAConclusionTruthDirectSelector_exists_of_native_trace :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence,
    RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence ->
    exists nextGlobalSigma nextGlobalPi : M,
    exists applicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma,
    exists conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters,
      RawDynamicTruthPairedGlobalSuccessorAt M
        currentGlobalSigma currentGlobalPi
        (raw_succ M predecessorLevel) nextGlobalSigma nextGlobalPi /\
      RawCodedTernaryPredicateDeepClosed M nextGlobalSigma /\
      (forall lower upper conclusion assignmentCode assignmentStep,
        rawCoqRestrictedPATruthDirectOutput conclusionTruth
          lower upper conclusion assignmentCode assignmentStep =
        rawTernaryApplicationOutput applicationSelector
          conclusion assignmentCode assignmentStep) /\
      (forall lower upper,
        rawCoqRestrictedPATruthDirectOutput conclusionTruth
          lower upper
          (rawQuotedTermCode M (tVar 0))
          (rawQuotedTermCode M tZero)
          (rawQuotedTermCode M tZero) =
        nextSigmaEvidence).
Proof.
  intros M hPA parameters tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    [hcurrentOrbit
      (currentLevel & nextGlobalSigma & nextGlobalPi & currentLevelNumeral &
       hcurrentLevel & hsuccessor & hcurrentLevelNumeral &
       hsigmaDomain & hpiDomain & hnativeApplication)].
  subst currentLevel.

  destruct
    (dynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitExists_all
      M hPA (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA)
      tail (raw_succ M predecessorLevel)) as
    (deepCurrentSigma & deepCurrentPi &
     hdeepCurrentOrbit & hdeepCurrentSigma & hdeepCurrentPi).
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_functional
      M hPA tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi
      deepCurrentSigma deepCurrentPi
      hcurrentOrbit hdeepCurrentOrbit) as
    [hcurrentSigma hcurrentPi].
  subst deepCurrentSigma. subst deepCurrentPi.

  destruct (dynamicTruthPairedGlobalSuccessorAt_deep_closed
    M hPA (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA)
    currentGlobalSigma currentGlobalPi (raw_succ M predecessorLevel)
    nextGlobalSigma nextGlobalPi
    hdeepCurrentSigma hdeepCurrentPi hsuccessor) as
    [hnextSigmaDeep _hnextPiDeep].

  destruct (raw_codedTernaryApplicationSelector_exists
    M hPA nextGlobalSigma (proj1 hnextSigmaDeep)) as
    [applicationSelector _].
  set (conclusionTruth :=
    rawCoqRestrictedPAConclusionTruthDirectSelector_of_ternary
      M hPA parameters nextGlobalSigma applicationSelector hnextSigmaDeep).
  exists nextGlobalSigma, nextGlobalPi,
    applicationSelector, conclusionTruth.
  split; [exact hsuccessor |].
  split; [exact hnextSigmaDeep |].
  split.
  - intros lower upper conclusion assignmentCode assignmentStep.
    unfold conclusionTruth.
    apply rawCoqRestrictedPAConclusionTruthDirectSelector_output.
  - intros lower upper.
    unfold conclusionTruth.
    rewrite rawCoqRestrictedPAConclusionTruthDirectSelector_output.
    apply (rawTernaryApplicationOutput_unique M hPA
      nextGlobalSigma applicationSelector
      (rawQuotedTermCode M (tVar 0))
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero)
      nextSigmaEvidence).
    + apply raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax.
      exact hPA.
    + apply raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax.
      exact hPA.
    + apply raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax.
      exact hPA.
    + apply (proj1
        (raw_dynamicTruthNativeAxiomApplication_ternary_iff
          M hPA nextGlobalSigma nextSigmaEvidence)).
      exact hnativeApplication.
Qed.

(** A compact corollary when only the exact direct selector and its native
    output equation are needed.  The existentially hidden predicate remains
    tied to the trace by the stronger theorem above; this projection does not
    manufacture an unrelated truth family. *)
Corollary
    raw_coqRestrictedPAConclusionTruthDirectSelector_native_output_exists :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence,
    RawDynamicTruthNativeAxiomSoundnessProofTraceAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence ->
    exists conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters,
      forall lower upper,
        rawCoqRestrictedPATruthDirectOutput conclusionTruth
          lower upper
          (rawQuotedTermCode M (tVar 0))
          (rawQuotedTermCode M tZero)
          (rawQuotedTermCode M tZero) =
        nextSigmaEvidence.
Proof.
  intros M hPA parameters tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence htrace.
  destruct
    (raw_coqRestrictedPAConclusionTruthDirectSelector_exists_of_native_trace
      M hPA parameters tail predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence htrace) as
    (nextGlobalSigma & nextGlobalPi & applicationSelector &
     conclusionTruth & hsuccessor & hdeep & houtput & hnative).
  exists conclusionTruth.
  exact hnative.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessConclusionTruthDirectSelector.
