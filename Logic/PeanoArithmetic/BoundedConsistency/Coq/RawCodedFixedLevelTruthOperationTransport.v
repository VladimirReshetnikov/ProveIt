(**
  Fixed-level truth interfaces for transparent formula operations.

  A de Bruijn operation does not preserve truth under an arbitrary pair of
  beta-coded assignments.  This file makes the missing assignment data
  explicit.  For a shift, source index [i] and target index [j] are related
  by the very [RawShiftedIndex] graph used in the term-operation trace.  For
  a single substitution, the input-side assignment is the output-side
  assignment prefixed by the value of the replacement term.

  The constructor skeleton of an operation determines hierarchy ranks, but
  the current arbitrary-model operation development exposes cross-trace
  rank agreement as a named seam.  We therefore represent rank agreement
  for one source/target pair and prove all domain and admissibility transport
  consequences from it.  We also represent the exact Sigma/Pi certificate
  transport law required by proof-rule soundness.  Importantly, merely
  packaging that law does not assert it: deriving it from a nonstandard term
  shift/opening trace requires a Tarski compatibility theorem for coded term
  evaluation which is not yet available.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedFormulaRankTraversal
  RawCodedFormulaRankRealization RawCodedFormulaRankTotality
  RawCodedFormulaOperations
  RawCodedTermEvaluationTraversal RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality.

Module PABoundedRawCodedFixedLevelTruthOperationTransport.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankRealization.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.

Definition operationTransportAnd3 (a b c : formula) : formula :=
  pAnd a (pAnd b c).

Definition operationTransportAnd5 (a b c d f : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d f))).

Definition operationTransportIff (a b : formula) : formula :=
  pAnd (pImp a b) (pImp b a).

Definition operationTransportAll3 (body : formula) : formula :=
  pAll (pAll (pAll body)).

Definition operationTransportAll4 (body : formula) : formula :=
  pAll (pAll (pAll (pAll body))).

(** ------------------------------------------------------------------
    Assignment graphs.

    [bound] bounds *source* variable indices.  The target index is computed
    by [RawShiftedIndex].  Requiring lookup equivalence, rather than only a
    forward implication, is exactly what is needed to rebuild atomic truth
    evidence in both directions. *)

Definition codedFormulaShiftAssignmentRelationTermAt
    (cutoff amount bound sourceCode sourceStep targetCode targetStep : term)
    : formula :=
  operationTransportAll3
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 bound))
      (pImp
        (codedShiftedIndexTermAt
          (liftTerm 3 cutoff) (liftTerm 3 amount)
          (tVar 2) (tVar 1))
        (operationTransportIff
          (codedAssignmentLookupTermAt
            (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
            (tVar 2) (tVar 0))
          (codedAssignmentLookupTermAt
            (liftTerm 3 targetCode) (liftTerm 3 targetStep)
            (tVar 1) (tVar 0))))).

Definition RawCodedFormulaShiftAssignmentRelation (M : RawPAModel)
    (cutoff amount bound sourceCode sourceStep targetCode targetStep : M)
    : Prop :=
  forall inputIndex outputIndex value : M,
    rawLt M inputIndex bound ->
    RawShiftedIndex M cutoff amount inputIndex outputIndex ->
    (RawCodedAssignmentLookup M sourceCode sourceStep inputIndex value <->
     RawCodedAssignmentLookup M targetCode targetStep outputIndex value).

Arguments RawCodedFormulaShiftAssignmentRelation
  M cutoff amount bound sourceCode sourceStep targetCode targetStep
  : clear implicits.

Lemma raw_sat_codedFormulaShiftAssignmentRelationTermAt_iff : forall
    (M : RawPAModel) e cutoff amount bound
    sourceCode sourceStep targetCode targetStep,
  raw_formula_sat M e
    (codedFormulaShiftAssignmentRelationTermAt
      cutoff amount bound sourceCode sourceStep targetCode targetStep) <->
  RawCodedFormulaShiftAssignmentRelation M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e bound)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep).
Proof.
  intros. unfold codedFormulaShiftAssignmentRelationTermAt,
    operationTransportAll3, operationTransportIff,
    RawCodedFormulaShiftAssignmentRelation.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedShiftedIndexTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. tauto.
Qed.

(** The proof-rule shift is the important special case: cutoff zero and
    amount one.  A beta prepend is a concrete realization of its assignment
    graph. *)
Lemma raw_add_zero_right_operationTransport : forall
    (M : RawPAModel), RawPASatisfies M -> forall value,
  raw_add M value (raw_zero M) = value.
Proof.
  intros M hPA value.
  set (e := scons M value (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_addZero_term nil (tVar 0)) e) as hadd.
  unfold e in hadd. cbn [raw_formula_sat raw_term_eval scons] in hadd.
  exact hadd.
Qed.

Theorem raw_codedFormulaUnitShiftAssignmentRelation_of_prepend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    bound sourceCode sourceStep head targetCode targetStep,
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound ->
  RawCodedAssignmentPrepend M
    sourceCode sourceStep head bound targetCode targetStep ->
  RawCodedFormulaShiftAssignmentRelation M
    (raw_zero M) (rawNumeralValue M 1) bound
    sourceCode sourceStep targetCode targetStep.
Proof.
  intros M hPA bound sourceCode sourceStep head targetCode targetStep
    hdefined hprepend inputIndex outputIndex value hindex hshifted.
  destruct hshifted as [[himpossible _] | [_ houtput]].
  - exfalso. exact (raw_not_lt_zero M hPA inputIndex himpossible).
  - assert (houtputSucc : outputIndex = raw_succ M inputIndex).
    {
      rewrite houtput.
      change (raw_add M inputIndex (raw_succ M (raw_zero M)) =
        raw_succ M inputIndex).
      rewrite raw_add_succ by exact hPA.
      rewrite raw_add_zero_right_operationTransport by exact hPA.
      reflexivity.
    }
    rewrite houtputSucc.
    symmetry.
    apply (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
      sourceCode sourceStep head bound targetCode targetStep
      hdefined hprepend inputIndex hindex value).
Qed.

(** For opening/substitution, [sourceCode/sourceStep] evaluate the formula
    before opening and [targetCode/targetStep] evaluate the result.  Thus the
    source assignment is the target assignment prefixed by the replacement
    value.  The value is certified under the target assignment. *)
Definition codedFormulaSubstitutionAssignmentRelationTermAt
    (replacement bound sourceCode sourceStep targetCode targetStep : term)
    : formula :=
  pEx
    (pAnd
      (termEvaluationCertificateTermAt
        (liftTerm 1 replacement) (tVar 0)
        (liftTerm 1 targetCode) (liftTerm 1 targetStep))
      (codedAssignmentPrependTermAt
        (liftTerm 1 targetCode) (liftTerm 1 targetStep)
        (tVar 0) (liftTerm 1 bound)
        (liftTerm 1 sourceCode) (liftTerm 1 sourceStep))).

Definition RawCodedFormulaSubstitutionAssignmentRelation
    (M : RawPAModel)
    (replacement bound sourceCode sourceStep targetCode targetStep : M)
    : Prop :=
  exists replacementValue : M,
    RawTermEvaluationCertificate M replacement replacementValue
      targetCode targetStep /\
    RawCodedAssignmentPrepend M
      targetCode targetStep replacementValue bound sourceCode sourceStep.

Arguments RawCodedFormulaSubstitutionAssignmentRelation
  M replacement bound sourceCode sourceStep targetCode targetStep
  : clear implicits.

Lemma raw_sat_codedFormulaSubstitutionAssignmentRelationTermAt_iff : forall
    (M : RawPAModel) e replacement bound
    sourceCode sourceStep targetCode targetStep,
  raw_formula_sat M e
    (codedFormulaSubstitutionAssignmentRelationTermAt
      replacement bound sourceCode sourceStep targetCode targetStep) <->
  RawCodedFormulaSubstitutionAssignmentRelation M
    (raw_term_eval M e replacement) (raw_term_eval M e bound)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep).
Proof.
  intros. unfold codedFormulaSubstitutionAssignmentRelationTermAt,
    RawCodedFormulaSubstitutionAssignmentRelation.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_termEvaluationCertificateTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentPrependTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Pairwise rank agreement and its concrete consequences. *)

Definition codedFormulaRankAgreementTermAt (source target : term)
    : formula :=
  operationTransportAll4
    (pImp
      (codedFormulaRankTermAt
        (liftTerm 4 source) (tVar 3) (tVar 2))
      (pImp
        (codedFormulaRankTermAt
          (liftTerm 4 target) (tVar 1) (tVar 0))
        (pAnd (pEq (tVar 1) (tVar 3))
          (pEq (tVar 0) (tVar 2))))).

Definition RawCodedFormulaRankAgreement (M : RawPAModel)
    (source target : M) : Prop :=
  forall sourceSigma sourcePi targetSigma targetPi : M,
    RawCodedFormulaRank M source sourceSigma sourcePi ->
    RawCodedFormulaRank M target targetSigma targetPi ->
    targetSigma = sourceSigma /\ targetPi = sourcePi.

Arguments RawCodedFormulaRankAgreement M source target : clear implicits.

Lemma raw_sat_codedFormulaRankAgreementTermAt_iff : forall
    (M : RawPAModel) e source target,
  raw_formula_sat M e (codedFormulaRankAgreementTermAt source target) <->
  RawCodedFormulaRankAgreement M
    (raw_term_eval M e source) (raw_term_eval M e target).
Proof.
  intros. unfold codedFormulaRankAgreementTermAt,
    operationTransportAll4, RawCodedFormulaRankAgreement.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaRankTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedFormulaRankAgreement_of_operationRankPreserving : forall
    (M : RawPAModel) atom,
  RawCodedFormulaOperationRankPreserving M atom ->
  forall parameter rootDepth source target,
    RawCodedFormulaOperation M atom parameter rootDepth source target ->
    RawCodedFormulaRankAgreement M source target.
Proof.
  intros M atom hpreserving parameter rootDepth source target hoperation.
  intros sourceSigma sourcePi targetSigma targetPi.
  exact (hpreserving parameter rootDepth source target
    sourceSigma sourcePi targetSigma targetPi hoperation).
Qed.

Corollary raw_codedFormulaShift_rankAgreement : forall
    (M : RawPAModel), RawCodedFormulaShiftRankPreserving M -> forall
    cutoff amount source target,
  RawCodedFormulaShift M cutoff amount source target ->
  RawCodedFormulaRankAgreement M source target.
Proof.
  intros M hpreserving cutoff amount source target hoperation
    sourceSigma sourcePi targetSigma targetPi.
  exact (hpreserving cutoff amount source target
    sourceSigma sourcePi targetSigma targetPi hoperation).
Qed.

Corollary raw_codedFormulaSingleSubstitution_rankAgreement : forall
    (M : RawPAModel),
  RawCodedFormulaSingleSubstitutionRankPreserving M -> forall
    replacement source target,
  RawCodedFormulaSingleSubstitution M replacement source target ->
  RawCodedFormulaRankAgreement M source target.
Proof.
  intros M hpreserving replacement source target hoperation
    sourceSigma sourcePi targetSigma targetPi.
  exact (hpreserving replacement source target
    sourceSigma sourcePi targetSigma targetPi hoperation).
Qed.

Theorem raw_fixedLevel_domains_iff_of_rankAgreement : forall
    (M : RawPAModel), RawPASatisfies M -> forall level source target,
  RawCodedWellFormedFormula M source ->
  RawCodedWellFormedFormula M target ->
  RawCodedFormulaRankAgreement M source target ->
  (RawFixedLevelSigmaDomain M level source <->
   RawFixedLevelSigmaDomain M level target) /\
  (RawFixedLevelPiDomain M level source <->
   RawFixedLevelPiDomain M level target).
Proof.
  intros M hPA level source target hsourceWellFormed htargetWellFormed
    hagreement.
  destruct (raw_codedWellFormedFormula_rank_exists M hPA source
    hsourceWellFormed) as (sourceSigma & sourcePi & hsourceRank).
  destruct (raw_codedWellFormedFormula_rank_exists M hPA target
    htargetWellFormed) as (targetSigma & targetPi & htargetRank).
  destruct (hagreement sourceSigma sourcePi targetSigma targetPi
    hsourceRank htargetRank) as [hsigma hpi].
  subst targetSigma. subst targetPi.
  split.
  - unfold RawFixedLevelSigmaDomain. split.
    + intros (sigma & pi & hrank & hbound).
      destruct (raw_codedFormulaRank_functional M hPA source
        sigma pi sourceSigma sourcePi hrank hsourceRank) as [-> ->].
      exists sourceSigma, sourcePi. split; assumption.
    + intros (sigma & pi & hrank & hbound).
      destruct (raw_codedFormulaRank_functional M hPA target
        sigma pi sourceSigma sourcePi hrank htargetRank) as [-> ->].
      exists sourceSigma, sourcePi. split; assumption.
  - unfold RawFixedLevelPiDomain. split.
    + intros (sigma & pi & hrank & hbound).
      destruct (raw_codedFormulaRank_functional M hPA source
        sigma pi sourceSigma sourcePi hrank hsourceRank) as [-> ->].
      exists sourceSigma, sourcePi. split; assumption.
    + intros (sigma & pi & hrank & hbound).
      destruct (raw_codedFormulaRank_functional M hPA target
        sigma pi sourceSigma sourcePi hrank htargetRank) as [-> ->].
      exists sourceSigma, sourcePi. split; assumption.
Qed.

Definition codedFormulaTargetAdmissibilityDataTermAt
    (target targetAssignmentCode targetAssignmentStep : term) : formula :=
  pAnd
    (codedFormulaAtomicallyAdequateTermAt target)
    (codedAssignmentDefinedThroughTermAt
      targetAssignmentCode targetAssignmentStep target).

Definition RawCodedFormulaTargetAdmissibilityData (M : RawPAModel)
    (target targetAssignmentCode targetAssignmentStep : M) : Prop :=
  RawCodedFormulaAtomicallyAdequate M target /\
  RawCodedAssignmentDefinedThrough M
    targetAssignmentCode targetAssignmentStep target.

Arguments RawCodedFormulaTargetAdmissibilityData
  M target targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_sat_codedFormulaTargetAdmissibilityDataTermAt_iff : forall
    (M : RawPAModel) e target targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (codedFormulaTargetAdmissibilityDataTermAt
      target targetAssignmentCode targetAssignmentStep) <->
  RawCodedFormulaTargetAdmissibilityData M
    (raw_term_eval M e target)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold codedFormulaTargetAdmissibilityDataTermAt,
    RawCodedFormulaTargetAdmissibilityData.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff,
    raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  reflexivity.
Qed.

Theorem raw_fixedLevelTruthAdmissible_transport_of_rankAgreement : forall
    (M : RawPAModel), RawPASatisfies M -> forall level source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaRankAgreement M source target ->
  RawFixedLevelTruthAdmissible M level
    source sourceAssignmentCode sourceAssignmentStep ->
  RawCodedFormulaTargetAdmissibilityData M
    target targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthAdmissible M level
    target targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA level source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep hagreement
    [hsourceAtomic [hsourceAssignment hsourceDomain]]
    [htargetAtomic htargetAssignment].
  assert (hsourceWellFormed : RawCodedWellFormedFormula M source).
  {
    destruct hsourceAtomic as
      (formulaCode & formulaStep & bound & rootIndex & hsyntax & _).
    exists formulaCode, formulaStep, bound, rootIndex. exact hsyntax.
  }
  assert (htargetWellFormed : RawCodedWellFormedFormula M target).
  {
    destruct htargetAtomic as
      (formulaCode & formulaStep & bound & rootIndex & hsyntax & _).
    exists formulaCode, formulaStep, bound, rootIndex. exact hsyntax.
  }
  destruct (raw_fixedLevel_domains_iff_of_rankAgreement M hPA level
    source target hsourceWellFormed htargetWellFormed hagreement)
    as [hsigma hpi].
  split; [exact htargetAtomic |].
  split; [exact htargetAssignment |].
  destruct hsourceDomain as [hsourceSigma | hsourcePi].
  - left. exact (proj1 hsigma hsourceSigma).
  - right. exact (proj1 hpi hsourcePi).
Qed.

(** ------------------------------------------------------------------
    Fixed-level certificate law.

    This is the precise Tarski seam: both truth polarities must be invariant
    under the operation-specific assignment graph.  It is a first-order PA
    formula for every external [level], so later work can prove and consume
    it without introducing a meta-level predicate into the arithmetization. *)

Definition fixedLevelTruthCertificateTransportTermAt (level : nat)
    (source target sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  pAnd
    (operationTransportIff
      (fixedLevelSigmaTruthCertificateTermAt level
        source sourceAssignmentCode sourceAssignmentStep)
      (fixedLevelSigmaTruthCertificateTermAt level
        target targetAssignmentCode targetAssignmentStep))
    (operationTransportIff
      (fixedLevelPiFalsityCertificateTermAt level
        source sourceAssignmentCode sourceAssignmentStep)
      (fixedLevelPiFalsityCertificateTermAt level
        target targetAssignmentCode targetAssignmentStep)).

Definition RawFixedLevelTruthCertificateTransport (M : RawPAModel)
    (level : nat)
    (source target sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  (RawFixedLevelSigmaTruthCertificate M level
      source sourceAssignmentCode sourceAssignmentStep <->
   RawFixedLevelSigmaTruthCertificate M level
      target targetAssignmentCode targetAssignmentStep) /\
  (RawFixedLevelPiFalsityCertificate M level
      source sourceAssignmentCode sourceAssignmentStep <->
   RawFixedLevelPiFalsityCertificate M level
      target targetAssignmentCode targetAssignmentStep).

Arguments RawFixedLevelTruthCertificateTransport
  M level source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_sat_fixedLevelTruthCertificateTransportTermAt_iff : forall
    (M : RawPAModel) e level source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (fixedLevelTruthCertificateTransportTermAt level
      source target sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawFixedLevelTruthCertificateTransport M level
    (raw_term_eval M e source) (raw_term_eval M e target)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold fixedLevelTruthCertificateTransportTermAt,
    operationTransportIff, RawFixedLevelTruthCertificateTransport.
  cbn [raw_formula_sat].
  rewrite !raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff,
    !raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  tauto.
Qed.

(** ------------------------------------------------------------------
    Represented, operation-specific readiness packages.

    The package stops immediately before the certificate Tarski law.  This
    boundary is intentional: everything in it follows from transparent
    syntax/rank/admissibility data already present in the development. *)

Definition fixedLevelFormulaShiftTransportReadyTermAt (level : nat)
    (cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  operationTransportAnd5
    (codedFormulaShiftTermAt cutoff amount source target)
    (codedFormulaShiftAssignmentRelationTermAt
      cutoff amount source sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep)
    (fixedLevelTruthAdmissibleTermAt level
      source sourceAssignmentCode sourceAssignmentStep)
    (codedFormulaTargetAdmissibilityDataTermAt
      target targetAssignmentCode targetAssignmentStep)
    (codedFormulaRankAgreementTermAt source target).

Definition RawFixedLevelFormulaShiftTransportReady (M : RawPAModel)
    (level : nat)
    (cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  RawCodedFormulaShift M cutoff amount source target /\
  RawCodedFormulaShiftAssignmentRelation M cutoff amount source
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep /\
  RawFixedLevelTruthAdmissible M level
    source sourceAssignmentCode sourceAssignmentStep /\
  RawCodedFormulaTargetAdmissibilityData M
    target targetAssignmentCode targetAssignmentStep /\
  RawCodedFormulaRankAgreement M source target.

Arguments RawFixedLevelFormulaShiftTransportReady
  M level cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_sat_fixedLevelFormulaShiftTransportReadyTermAt_iff : forall
    (M : RawPAModel) e level cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (fixedLevelFormulaShiftTransportReadyTermAt level
      cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawFixedLevelFormulaShiftTransportReady M level
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e source) (raw_term_eval M e target)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold fixedLevelFormulaShiftTransportReadyTermAt,
    operationTransportAnd5, RawFixedLevelFormulaShiftTransportReady.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaShiftTermAt_iff,
    raw_sat_codedFormulaShiftAssignmentRelationTermAt_iff,
    raw_sat_fixedLevelTruthAdmissibleTermAt_iff,
    raw_sat_codedFormulaTargetAdmissibilityDataTermAt_iff,
    raw_sat_codedFormulaRankAgreementTermAt_iff.
  reflexivity.
Qed.

Theorem raw_fixedLevelFormulaShiftTransportReady_target_admissible : forall
    (M : RawPAModel), RawPASatisfies M -> forall level
      cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawFixedLevelFormulaShiftTransportReady M level
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthAdmissible M level
    target targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA level cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    [_ [_ [hsource [htarget hagreement]]]].
  exact (raw_fixedLevelTruthAdmissible_transport_of_rankAgreement
    M hPA level source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hagreement hsource htarget).
Qed.

Theorem raw_fixedLevelFormulaShiftTransportReady_of_rankPreservation : forall
    (M : RawPAModel), RawCodedFormulaShiftRankPreserving M -> forall level
      cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaShift M cutoff amount source target ->
  RawCodedFormulaShiftAssignmentRelation M cutoff amount source
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthAdmissible M level
    source sourceAssignmentCode sourceAssignmentStep ->
  RawCodedFormulaTargetAdmissibilityData M
    target targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelFormulaShiftTransportReady M level
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hpreserving level cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hoperation hassignments hsource htarget.
  split; [exact hoperation |].
  split; [exact hassignments |].
  split; [exact hsource |].
  split; [exact htarget |].
  exact (raw_codedFormulaShift_rankAgreement M hpreserving cutoff amount
    source target hoperation).
Qed.

Definition fixedLevelFormulaSubstitutionTransportReadyTermAt (level : nat)
    (replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  operationTransportAnd5
    (codedFormulaSingleSubstitutionTermAt replacement source target)
    (codedFormulaSubstitutionAssignmentRelationTermAt
      replacement source sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep)
    (fixedLevelTruthAdmissibleTermAt level
      source sourceAssignmentCode sourceAssignmentStep)
    (codedFormulaTargetAdmissibilityDataTermAt
      target targetAssignmentCode targetAssignmentStep)
    (codedFormulaRankAgreementTermAt source target).

Definition RawFixedLevelFormulaSubstitutionTransportReady
    (M : RawPAModel) (level : nat)
    (replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  RawCodedFormulaSingleSubstitution M replacement source target /\
  RawCodedFormulaSubstitutionAssignmentRelation M replacement source
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep /\
  RawFixedLevelTruthAdmissible M level
    source sourceAssignmentCode sourceAssignmentStep /\
  RawCodedFormulaTargetAdmissibilityData M
    target targetAssignmentCode targetAssignmentStep /\
  RawCodedFormulaRankAgreement M source target.

Arguments RawFixedLevelFormulaSubstitutionTransportReady
  M level replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_sat_fixedLevelFormulaSubstitutionTransportReadyTermAt_iff : forall
    (M : RawPAModel) e level replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (fixedLevelFormulaSubstitutionTransportReadyTermAt level
      replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawFixedLevelFormulaSubstitutionTransportReady M level
    (raw_term_eval M e replacement)
    (raw_term_eval M e source) (raw_term_eval M e target)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold fixedLevelFormulaSubstitutionTransportReadyTermAt,
    operationTransportAnd5,
    RawFixedLevelFormulaSubstitutionTransportReady.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff,
    raw_sat_codedFormulaSubstitutionAssignmentRelationTermAt_iff,
    raw_sat_fixedLevelTruthAdmissibleTermAt_iff,
    raw_sat_codedFormulaTargetAdmissibilityDataTermAt_iff,
    raw_sat_codedFormulaRankAgreementTermAt_iff.
  reflexivity.
Qed.

Theorem raw_fixedLevelFormulaSubstitutionTransportReady_target_admissible :
  forall (M : RawPAModel), RawPASatisfies M -> forall level
      replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawFixedLevelFormulaSubstitutionTransportReady M level
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthAdmissible M level
    target targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA level replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    [_ [_ [hsource [htarget hagreement]]]].
  exact (raw_fixedLevelTruthAdmissible_transport_of_rankAgreement
    M hPA level source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hagreement hsource htarget).
Qed.

Theorem
    raw_fixedLevelFormulaSubstitutionTransportReady_of_rankPreservation :
  forall (M : RawPAModel),
  RawCodedFormulaSingleSubstitutionRankPreserving M -> forall level
      replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  RawCodedFormulaSingleSubstitution M replacement source target ->
  RawCodedFormulaSubstitutionAssignmentRelation M replacement source
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthAdmissible M level
    source sourceAssignmentCode sourceAssignmentStep ->
  RawCodedFormulaTargetAdmissibilityData M
    target targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelFormulaSubstitutionTransportReady M level
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hpreserving level replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep
    hoperation hassignments hsource htarget.
  split; [exact hoperation |].
  split; [exact hassignments |].
  split; [exact hsource |].
  split; [exact htarget |].
  exact (raw_codedFormulaSingleSubstitution_rankAgreement M hpreserving
    replacement source target hoperation).
Qed.

(** These two implications are the exact remaining arbitrary-model Tarski
    statements.  They are definitions, not assumptions.  Their represented
    term forms let the future 17-case rule proof cite precisely the required
    instance at its current formula and assignments. *)

Definition fixedLevelFormulaShiftTarskiStepTermAt (level : nat)
    (cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  pImp
    (fixedLevelFormulaShiftTransportReadyTermAt level
      cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep)
    (fixedLevelTruthCertificateTransportTermAt level
      source target sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep).

Definition RawFixedLevelFormulaShiftTarskiStep (M : RawPAModel)
    (level : nat)
    (cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  RawFixedLevelFormulaShiftTransportReady M level
    cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M level
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.

Arguments RawFixedLevelFormulaShiftTarskiStep
  M level cutoff amount source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_sat_fixedLevelFormulaShiftTarskiStepTermAt_iff : forall
    (M : RawPAModel) e level cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (fixedLevelFormulaShiftTarskiStepTermAt level
      cutoff amount source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawFixedLevelFormulaShiftTarskiStep M level
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e source) (raw_term_eval M e target)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold fixedLevelFormulaShiftTarskiStepTermAt,
    RawFixedLevelFormulaShiftTarskiStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelFormulaShiftTransportReadyTermAt_iff,
    raw_sat_fixedLevelTruthCertificateTransportTermAt_iff.
  tauto.
Qed.

Definition fixedLevelFormulaSubstitutionTarskiStepTermAt (level : nat)
    (replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : term) : formula :=
  pImp
    (fixedLevelFormulaSubstitutionTransportReadyTermAt level
      replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep)
    (fixedLevelTruthCertificateTransportTermAt level
      source target sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep).

Definition RawFixedLevelFormulaSubstitutionTarskiStep (M : RawPAModel)
    (level : nat)
    (replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep : M) : Prop :=
  RawFixedLevelFormulaSubstitutionTransportReady M level
    replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep ->
  RawFixedLevelTruthCertificateTransport M level
    source target sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep.

Arguments RawFixedLevelFormulaSubstitutionTarskiStep
  M level replacement source target
    sourceAssignmentCode sourceAssignmentStep
    targetAssignmentCode targetAssignmentStep : clear implicits.

Lemma raw_sat_fixedLevelFormulaSubstitutionTarskiStepTermAt_iff : forall
    (M : RawPAModel) e level replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep,
  raw_formula_sat M e
    (fixedLevelFormulaSubstitutionTarskiStepTermAt level
      replacement source target
      sourceAssignmentCode sourceAssignmentStep
      targetAssignmentCode targetAssignmentStep) <->
  RawFixedLevelFormulaSubstitutionTarskiStep M level
    (raw_term_eval M e replacement)
    (raw_term_eval M e source) (raw_term_eval M e target)
    (raw_term_eval M e sourceAssignmentCode)
    (raw_term_eval M e sourceAssignmentStep)
    (raw_term_eval M e targetAssignmentCode)
    (raw_term_eval M e targetAssignmentStep).
Proof.
  intros. unfold fixedLevelFormulaSubstitutionTarskiStepTermAt,
    RawFixedLevelFormulaSubstitutionTarskiStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelFormulaSubstitutionTransportReadyTermAt_iff,
    raw_sat_fixedLevelTruthCertificateTransportTermAt_iff.
  tauto.
Qed.

End PABoundedRawCodedFixedLevelTruthOperationTransport.
