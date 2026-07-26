(**
  Restricted local proof fields selected from the deep-closed global orbit.

  The earlier public field modules expose compiler interfaces quantified over
  every adequate witness of the ordinary paired orbit.  Deep-closure
  induction, however, gives an existentially selected orbit witness carrying
  the stronger operation invariant.  This file consumes that witness
  directly.  Consequently no functionality or uniqueness theorem for the
  ordinary orbit is needed merely to transfer closure to a different witness.

  The only algebraic input displayed here is the generic implication from
  ternary deep closure to opening interchange.  Shift interchange is already
  unconditional.  A separate concrete-algebra module discharges the opening
  input; keeping the reduction explicit makes the dependency boundary easy
  to audit.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedFixedLevelTruthTotality
  RawCodedNumeralTermCode
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthUniversalLeafProofCompilation
  RawCodedDynamicTruthUniversalLeafTransformGraph
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthPiExistentialLeafProofCompilation
  RawCodedDynamicTruthPiExistentialLeafTransformGraph
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedTernaryPredicateDeepClosure
  RawCodedTernaryPredicateDeepClosureShiftInterchange
  RawCodedTernaryPredicateDeepClosureOpeningCommuting
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthGlobalSuccessorDeepClosure
  RawCodedDynamicTruthPairedSuccessorLocalDeepClosure
  RawCodedDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitGraph
  RawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph
  RawCodedDynamicTruthRestrictedExistentialLocalProofFieldGraph.

Module
  PABoundedRawCodedDynamicTruthDeepClosedRestrictedLocalProofFields.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.
Import PABoundedRawCodedDynamicTruthUniversalLeafTransformGraph.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPiExistentialLeafProofCompilation.
Import PABoundedRawCodedDynamicTruthPiExistentialLeafTransformGraph.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedTernaryPredicateDeepClosureShiftInterchange.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningCommuting.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
Import PABoundedRawCodedDynamicTruthPairedSuccessorLocalDeepClosure.
Import
  PABoundedRawCodedDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitGraph.
Import
  PABoundedRawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph.
Import
  PABoundedRawCodedDynamicTruthRestrictedExistentialLocalProofFieldGraph.

(** This is the exact remaining algebraic interface at this layer.  It is
    intentionally stated only for deeply closed predicates, rather than for
    every atomically adequate formula code in an arbitrary PA model. *)
Definition RawCodedTernaryPredicateDeepClosedOpeningInterchangeTotal
    (M : RawPAModel) : Prop :=
  forall predicate,
    RawCodedTernaryPredicateDeepClosed M predicate ->
    RawCodedTernaryApplicationOpeningInterchange M predicate.

Arguments RawCodedTernaryPredicateDeepClosedOpeningInterchangeTotal M
  : clear implicits.

(** The represented substitution algebra discharges the preceding interface
    uniformly in every PA model. *)
Corollary
    raw_codedTernaryPredicateDeepClosedOpeningInterchangeTotal_of_PA :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedTernaryPredicateDeepClosedOpeningInterchangeTotal M.
Proof.
  intros M hPA predicate hdeep.
  exact
    (raw_codedTernaryApplicationOpeningInterchange_of_deepClosed_concrete
      M hPA predicate hdeep).
Qed.

(** Select the stronger orbit invariant at the requested carrier level and
    expose the ordinary adequate orbit together with all four operation laws
    consumed by the two restricted translators. *)
Theorem
    dynamicTruthPairedGlobalDeepClosedOrbit_interchange_exists :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawCodedTernaryPredicateDeepClosedOpeningInterchangeTotal M ->
  forall (tail : nat -> M) level,
  exists globalSigmaCode globalPiCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail level globalSigmaCode globalPiCode /\
    RawCodedTernaryApplicationShiftInterchange M globalSigmaCode /\
    RawCodedTernaryApplicationOpeningInterchange M globalSigmaCode /\
    RawCodedTernaryApplicationShiftInterchange M globalPiCode /\
    RawCodedTernaryApplicationOpeningInterchange M globalPiCode.
Proof.
  intros M hPA hlocalClosure hopening tail level.
  destruct
    (dynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitExists_all
      M hPA hlocalClosure tail level) as
    (globalSigmaCode & globalPiCode & hdeepOrbit).
  unfold RawDynamicTruthPairedGlobalDeepClosedFormulaCodeOrbitAt in
    hdeepOrbit.
  destruct hdeepOrbit as
    [hadequateOrbit [hglobalSigmaDeep hglobalPiDeep]].
  exists globalSigmaCode, globalPiCode.
  split; [exact hadequateOrbit |].
  repeat split.
  - exact
      (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
        M hPA globalSigmaCode hglobalSigmaDeep).
  - exact (hopening globalSigmaCode hglobalSigmaDeep).
  - exact
      (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
        M hPA globalPiCode hglobalPiDeep).
  - exact (hopening globalPiCode hglobalPiDeep).
Qed.

(** Proof-producing totality for the Sigma universal projection.  Notice
    that the selected deep-closed Pi coordinate is used immediately; we do
    not replace it by an arbitrary adequate witness of the ordinary orbit. *)
Theorem
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total_of_deep_closed_orbit
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawCodedTernaryPredicateDeepClosedOpeningInterchangeTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M.
Proof.
  intros M hPA hlocalClosure hopening tail level.
  destruct
    (dynamicTruthPairedGlobalDeepClosedOrbit_interchange_exists
      M hPA hlocalClosure hopening tail level) as
    (globalSigmaCode & globalPiCode & hadequateOrbit &
     hglobalSigmaShift & hglobalSigmaOpening &
     hglobalPiShift & hglobalPiOpening).
  pose proof (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigmaCode globalPiCode) hadequateOrbit) as
    horbitView.
  destruct horbitView as
    [horbit [hglobalSigmaAdequate hglobalPiAdequate]].
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (raw_dynamicTruthSigmaDomain_exists_adequate M hPA
    level upperNumeral hupperNumeral) as
    (domain & hdomain & _hdomainAdequate).
  destruct (raw_dynamicTruthSigmaLower_exists_adequate M hPA
    globalPiCode hglobalPiAdequate) as
    (lowerApplication & hlowerApplication & _hlowerAdequate).
  destruct (raw_codedTernaryApplicationSelector_exists M hPA
    globalPiCode hglobalPiAdequate) as [selector _hselector].
  assert (commutingOnSyntax :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
        globalPiCode selector).
  {
    constructor.
    - exact (rawTernaryApplicationSelector_shift_commuting_on_syntax
        M hPA globalPiCode selector hglobalPiShift).
    - exact (rawTernaryApplicationSelector_opening_commuting_on_syntax
        M hPA globalPiCode selector hglobalPiOpening).
  }
  destruct
    (rawDynamicTruthSigmaRestrictedUniversalDirectCompiler_of_selector
      M hPA globalPiCode level upperNumeral domain lowerApplication
      selector commutingOnSyntax hupperNumeral hdomain
      hlowerApplication) as [inputs identification].
  exists
    (rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
      domain lowerApplication),
    (rawCoqDynamicTruthSigmaRestrictedUniversalFieldCertificate
      M hPA inputs).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_iff
        M tail level
        (rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode M
          domain lowerApplication))).
    exists globalSigmaCode, globalPiCode. split; [exact horbit |].
    exists upperNumeral, domain, lowerApplication.
    repeat split; try assumption; reflexivity.
  - rewrite
      (rawDynamicTruthSigmaRestrictedUniversalFieldGraphCode_eq_compiled
        M hPA domain lowerApplication).
    exact
      (raw_codedPAProofOf_coqDynamicTruthSigmaRestrictedUniversalField_identified
        M hPA inputs domain lowerApplication identification).
Qed.

(** The Pi existential projection is symmetric: it consumes the Sigma
    coordinate of exactly the same selected deep-closed paired orbit. *)
Theorem
    dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_proof_total_of_deep_closed_orbit
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawCodedTernaryPredicateDeepClosedOpeningInterchangeTotal M ->
  RawDynamicTruthPiRestrictedExistentialLocalProofFieldTotal M.
Proof.
  intros M hPA hlocalClosure hopening tail level.
  destruct
    (dynamicTruthPairedGlobalDeepClosedOrbit_interchange_exists
      M hPA hlocalClosure hopening tail level) as
    (globalSigmaCode & globalPiCode & hadequateOrbit &
     hglobalSigmaShift & hglobalSigmaOpening &
     hglobalPiShift & hglobalPiOpening).
  pose proof (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
      tail level globalSigmaCode globalPiCode) hadequateOrbit) as
    horbitView.
  destruct horbitView as
    [horbit [hglobalSigmaAdequate hglobalPiAdequate]].
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M level)) as [upperNumeral hupperNumeral].
  destruct (raw_dynamicTruthPiDomain_exists_adequate M hPA
    level upperNumeral hupperNumeral) as
    (domain & hdomain & _hdomainAdequate).
  destruct (raw_dynamicTruthPiLower_exists_adequate M hPA
    globalSigmaCode hglobalSigmaAdequate) as
    (lowerApplication & hlowerApplication & _hlowerAdequate).
  destruct (raw_codedTernaryApplicationSelector_exists M hPA
    globalSigmaCode hglobalSigmaAdequate) as [selector _hselector].
  assert (commutingOnSyntax :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
        globalSigmaCode selector).
  {
    constructor.
    - exact (rawTernaryApplicationSelector_shift_commuting_on_syntax
        M hPA globalSigmaCode selector hglobalSigmaShift).
    - exact (rawTernaryApplicationSelector_opening_commuting_on_syntax
        M hPA globalSigmaCode selector hglobalSigmaOpening).
  }
  destruct
    (raw_coqDynamicTruthPiDirectTemplateIdentification_exists
      M hPA level (raw_succ M level) globalSigmaCode upperNumeral
      domain lowerApplication selector commutingOnSyntax
      hupperNumeral hdomain hlowerApplication) as
    [inputs identification].
  exists
    (rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
      domain lowerApplication),
    (rawCoqDynamicTruthPiRestrictedExistentialFieldCertificate
      M hPA inputs).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_iff
        M tail level
        (rawDynamicTruthPiRestrictedExistentialFieldGraphCode M
          domain lowerApplication))).
    exists globalSigmaCode, globalPiCode. split; [exact horbit |].
    exists upperNumeral, domain, lowerApplication.
    repeat split; try assumption; reflexivity.
  - rewrite
      (rawDynamicTruthPiRestrictedExistentialFieldGraphCode_eq_compiled
        M hPA domain lowerApplication).
    exact
      (raw_codedPAProofOf_coqDynamicTruthPiRestrictedExistentialField_identified
        M hPA inputs domain lowerApplication identification).
Qed.

(** A compact package for the two currently compiled positive-row
    projections.  These remain restricted row components, not the full
    Sigma/Pi local decision fields. *)
Corollary
    dynamicTruthDeepClosedRestrictedLocalProofFields_raw_proof_total :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawCodedTernaryPredicateDeepClosedOpeningInterchangeTotal M ->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M /\
  RawDynamicTruthPiRestrictedExistentialLocalProofFieldTotal M.
Proof.
  intros M hPA hlocalClosure hopening. split.
  - exact
      (dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total_of_deep_closed_orbit
        M hPA hlocalClosure hopening).
  - exact
      (dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_proof_total_of_deep_closed_orbit
        M hPA hlocalClosure hopening).
Qed.

(** Concrete endpoint of this reduction: after the opening algebra has been
    discharged, the paired local-row deep-closure callback is the sole
    remaining premise for both restricted proof fields. *)
Corollary
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total_of_local_closure
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M.
Proof.
  intros M hPA hlocalClosure.
  exact
    (dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total_of_deep_closed_orbit
      M hPA hlocalClosure
      (raw_codedTernaryPredicateDeepClosedOpeningInterchangeTotal_of_PA
        M hPA)).
Qed.

Corollary
    dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_proof_total_of_local_closure
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawDynamicTruthPiRestrictedExistentialLocalProofFieldTotal M.
Proof.
  intros M hPA hlocalClosure.
  exact
    (dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_proof_total_of_deep_closed_orbit
      M hPA hlocalClosure
      (raw_codedTernaryPredicateDeepClosedOpeningInterchangeTotal_of_PA
        M hPA)).
Qed.

Corollary
    dynamicTruthDeepClosedRestrictedLocalProofFields_raw_proof_total_of_local_closure
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPairedGlobalSuccessorLocalDeepClosure M ->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M /\
  RawDynamicTruthPiRestrictedExistentialLocalProofFieldTotal M.
Proof.
  intros M hPA hlocalClosure.
  exact
    (dynamicTruthDeepClosedRestrictedLocalProofFields_raw_proof_total
      M hPA hlocalClosure
      (raw_codedTernaryPredicateDeepClosedOpeningInterchangeTotal_of_PA
        M hPA)).
Qed.

(** Final unconditional endpoints for the two restricted row components.
    The preceding module now derives the only remaining local-closure input
    directly from PA, so callers no longer have to supply an operation law. *)
Corollary
    dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total_unconditional
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M.
Proof.
  intros M hPA.
  exact
    (dynamicTruthSigmaRestrictedUniversalLocalProofFieldGraph_raw_proof_total_of_local_closure
      M hPA
      (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA)).
Qed.

Corollary
    dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_proof_total_unconditional
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthPiRestrictedExistentialLocalProofFieldTotal M.
Proof.
  intros M hPA.
  exact
    (dynamicTruthPiRestrictedExistentialLocalProofFieldGraph_raw_proof_total_of_local_closure
      M hPA
      (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA)).
Qed.

Corollary
    dynamicTruthDeepClosedRestrictedLocalProofFields_raw_proof_total_unconditional
  : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthSigmaRestrictedUniversalLocalProofFieldTotal M /\
  RawDynamicTruthPiRestrictedExistentialLocalProofFieldTotal M.
Proof.
  intros M hPA.
  exact
    (dynamicTruthDeepClosedRestrictedLocalProofFields_raw_proof_total_of_local_closure
      M hPA
      (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA)).
Qed.

End
  PABoundedRawCodedDynamicTruthDeepClosedRestrictedLocalProofFields.
