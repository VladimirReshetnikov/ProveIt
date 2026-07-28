(**
  The aligned quantifier-free collision in the native dynamic-truth rows.

  The Sigma and Pi successor rows use the same formula code and assignment
  pair in their quantifier-free alternatives, but demand opposite outputs
  from the rank-zero evaluator.  Functionality of that evaluator therefore
  gives the exact local implication

      SigmaQF -> PiQF -> bottom.

  We first state the implication with only its three genuine inputs free.
  Shifting those variables by eight lands literally on the native row layout
  [#10], [#9], [#8] beneath the eight existential row witnesses.  No claim is
  made here about the other row branches or about a complete local field.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedRankZeroTruthTraversal
  RawCodedFixedLevelTruthLaws
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedPAProvability
  RawCodedRestrictedPAProof
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedPAProofImpICertificates
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedDynamicTruthPairedSuccessorAdequacy.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthQFBranchExclusivity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.

(** ------------------------------------------------------------------
    Three-input core and its exact native-row placement. *)

Definition dynamicTruthAlignedSigmaQFFormula : formula :=
  rankZeroTruthCertificateTermAt
    (tVar 2) (Term.numeral 1) (tVar 1) (tVar 0).

Definition dynamicTruthAlignedPiQFFormula : formula :=
  rankZeroTruthCertificateTermAt
    (tVar 2) tZero (tVar 1) (tVar 0).

Definition dynamicTruthQFBranchExclusivityFormula : formula :=
  pImp dynamicTruthAlignedSigmaQFFormula
    (pImp dynamicTruthAlignedPiQFFormula pBot).

(** The eight witnesses of either native row precede the shared root and
    assignment inputs. *)
Definition dynamicTruthQFRowRenaming (index : nat) : nat := index + 8.

Definition dynamicTruthQFRowBranchExclusivityFormula : formula :=
  pImp dynamicTruthSigmaRowQfFormula
    (pImp dynamicTruthPiRowQfFormula pBot).

(** These are the genuine selected row branches: the native successor rows
    quantify eight table witnesses before testing the branch disjunction.
    The QF leaves ignore those witnesses and read the aligned outer triple. *)
Definition dynamicTruthSigmaQFEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthSigmaRowQfFormula.

Definition dynamicTruthPiQFEx8BranchFormula : formula :=
  fixedLevelEx8 dynamicTruthPiRowQfFormula.

Definition dynamicTruthQFEx8BranchExclusivityFormula : formula :=
  pImp dynamicTruthSigmaQFEx8BranchFormula
    (pImp dynamicTruthPiQFEx8BranchFormula pBot).

Lemma dynamicTruthAlignedSigmaQFFormula_row_rename :
  Formula.rename dynamicTruthQFRowRenaming
    dynamicTruthAlignedSigmaQFFormula =
  dynamicTruthSigmaRowQfFormula.
Proof.
  reflexivity.
Qed.

Lemma dynamicTruthAlignedPiQFFormula_row_rename :
  Formula.rename dynamicTruthQFRowRenaming
    dynamicTruthAlignedPiQFFormula =
  dynamicTruthPiRowQfFormula.
Proof.
  reflexivity.
Qed.

Lemma dynamicTruthQFBranchExclusivityFormula_row_rename :
  Formula.rename dynamicTruthQFRowRenaming
    dynamicTruthQFBranchExclusivityFormula =
  dynamicTruthQFRowBranchExclusivityFormula.
Proof.
  reflexivity.
Qed.

(** Exact semantics of the three-input implication. *)
Lemma raw_sat_dynamicTruthQFBranchExclusivityFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthQFBranchExclusivityFormula <->
  (RawRankZeroTruthCertificate M
      (e 2) (rawNumeralValue M 1) (e 1) (e 0) ->
   RawRankZeroTruthCertificate M
      (e 2) (raw_zero M) (e 1) (e 0) -> False).
Proof.
  intros M e.
  unfold dynamicTruthQFBranchExclusivityFormula,
    dynamicTruthAlignedSigmaQFFormula,
    dynamicTruthAlignedPiQFFormula.
  cbn [raw_formula_sat raw_term_eval].
  rewrite !raw_sat_rankZeroTruthCertificateTermAt_iff.
  cbn [raw_term_eval].
  reflexivity.
Qed.

Theorem dynamicTruthQFBranchExclusivityFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e dynamicTruthQFBranchExclusivityFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_dynamicTruthQFBranchExclusivityFormula_iff M e)).
  intros hsigma hpi.
  exact (raw_rankZeroTruthCertificate_one_zero_exclusive M hPA
    (e 2) (e 1) (e 0) hsigma hpi).
Qed.

(** Exact semantics after retaining the native eight existential binders on
    each side.  The witnesses may differ; alignment concerns only the shared
    formula and assignment inputs outside those binders. *)
Lemma raw_sat_dynamicTruthSigmaQFEx8BranchFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthSigmaQFEx8BranchFormula <->
  exists a0 a1 a2 a3 a4 a5 a6 a7 : M,
    RawRankZeroTruthCertificate M
      (e 2) (rawNumeralValue M 1) (e 1) (e 0).
Proof.
  intros M e.
  unfold dynamicTruthSigmaQFEx8BranchFormula,
    dynamicTruthSigmaRowQfFormula, fixedLevelEx8.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_rankZeroTruthCertificateTermAt_iff.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Lemma raw_sat_dynamicTruthPiQFEx8BranchFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthPiQFEx8BranchFormula <->
  exists a0 a1 a2 a3 a4 a5 a6 a7 : M,
    RawRankZeroTruthCertificate M
      (e 2) (raw_zero M) (e 1) (e 0).
Proof.
  intros M e.
  unfold dynamicTruthPiQFEx8BranchFormula,
    dynamicTruthPiRowQfFormula, fixedLevelEx8.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_rankZeroTruthCertificateTermAt_iff.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Lemma raw_sat_dynamicTruthQFEx8BranchExclusivityFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthQFEx8BranchExclusivityFormula <->
  ((exists a0 a1 a2 a3 a4 a5 a6 a7 : M,
      RawRankZeroTruthCertificate M
        (e 2) (rawNumeralValue M 1) (e 1) (e 0)) ->
   (exists b0 b1 b2 b3 b4 b5 b6 b7 : M,
      RawRankZeroTruthCertificate M
        (e 2) (raw_zero M) (e 1) (e 0)) -> False).
Proof.
  intros M e.
  unfold dynamicTruthQFEx8BranchExclusivityFormula,
    dynamicTruthSigmaQFEx8BranchFormula,
    dynamicTruthPiQFEx8BranchFormula,
    dynamicTruthSigmaRowQfFormula,
    dynamicTruthPiRowQfFormula,
    fixedLevelEx8.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_rankZeroTruthCertificateTermAt_iff.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Theorem dynamicTruthQFEx8BranchExclusivityFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e dynamicTruthQFEx8BranchExclusivityFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_dynamicTruthQFEx8BranchExclusivityFormula_iff M e)).
  intros (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hsigma)
    (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & hpi).
  exact (raw_rankZeroTruthCertificate_one_zero_exclusive M hPA
    (e 2) (e 1) (e 0) hsigma hpi).
Qed.

(** ------------------------------------------------------------------
    Ordinary PA proof, derived from the published functionality theorem. *)

Theorem PA_proves_dynamicTruthQFBranchExclusivityFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthQFBranchExclusivityFormula.
Proof.
  apply Formula.BProv_impI.
  apply Formula.BProv_impI.
  set (G := [dynamicTruthAlignedPiQFFormula;
             dynamicTruthAlignedSigmaQFFormula]).
  assert (hfunctional : Formula.BProv Formula.Ax_s G
      rankZeroTruthCertificateFunctionalFormula).
  {
    apply Formula.BProv_weaken_nil.
    exact PA_proves_rankZeroTruthCertificateFunctionalFormula.
  }
  pose proof (Formula.BProv_allE Formula.Ax_s G _ (tVar 2)
    hfunctional) as hroot.
  pose proof (Formula.BProv_allE Formula.Ax_s G _ (tVar 1)
    hroot) as hassignmentCode.
  pose proof (Formula.BProv_allE Formula.Ax_s G _ (tVar 0)
    hassignmentCode) as hassignmentStep.
  pose proof (Formula.BProv_allE Formula.Ax_s G _ (Term.numeral 1)
    hassignmentStep) as hone.
  pose proof (Formula.BProv_allE Formula.Ax_s G _ tZero hone) as hzero.
  cbn in hzero.
  repeat rewrite term_subst_instTerm_rename_succ in hzero.
  assert (hsigma : Formula.BProv Formula.Ax_s G
      dynamicTruthAlignedSigmaQFFormula).
  {
    apply Formula.BProv_ass.
    unfold G. cbn. tauto.
  }
  assert (hpi : Formula.BProv Formula.Ax_s G
      dynamicTruthAlignedPiQFFormula).
  {
    apply Formula.BProv_ass.
    unfold G. cbn. tauto.
  }
  assert (hpair : Formula.BProv Formula.Ax_s G
      (pAnd dynamicTruthAlignedSigmaQFFormula
        dynamicTruthAlignedPiQFFormula)).
  {
    exact (Formula.BProv_andI Formula.Ax_s G _ _ hsigma hpi).
  }
  pose proof (Formula.BProv_mp Formula.Ax_s G _ _ hzero hpair)
    as hequality.
  exact (Formula.BProv_Ax_s_eq_succ_eq_zero_bot G
    (Term.numeral 1) tZero
    (Formula.BProv_eqRefl Formula.Ax_s G (Term.numeral 1))
    hequality).
Qed.

(** Renaming by eight is legitimate because every PA axiom is a sentence.
    The empty context remains empty, so this is an ordinary proof of the
    literal implication between the two native QF row leaves. *)
Theorem PA_proves_dynamicTruthQFRowBranchExclusivityFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthQFRowBranchExclusivityFormula.
Proof.
  rewrite <- dynamicTruthQFBranchExclusivityFormula_row_rename.
  exact (Formula.BProv_rename_of_sentences
    Formula.Ax_s Formula.sentence_ax_s []
    dynamicTruthQFBranchExclusivityFormula
    PA_proves_dynamicTruthQFBranchExclusivityFormula
    dynamicTruthQFRowRenaming).
Qed.

(** ------------------------------------------------------------------
    Closed-completeness route for the genuine Ex8 branch implication. *)

Definition dynamicTruthQFEx8BranchExclusivityFormula_closed : formula :=
  Formula.sealPA dynamicTruthQFEx8BranchExclusivityFormula.

Lemma dynamicTruthQFEx8BranchExclusivityFormula_closed_sentence :
  Formula.Sentence dynamicTruthQFEx8BranchExclusivityFormula_closed.
Proof.
  unfold dynamicTruthQFEx8BranchExclusivityFormula_closed.
  apply Formula.sealPA_sentence.
Qed.

Lemma dynamicTruthQFEx8BranchExclusivityFormula_closed_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    dynamicTruthQFEx8BranchExclusivityFormula_closed.
Proof.
  intros M hPA e.
  unfold dynamicTruthQFEx8BranchExclusivityFormula_closed.
  apply raw_formula_sat_sealPA_of_valid.
  intro inner.
  exact (dynamicTruthQFEx8BranchExclusivityFormula_raw_valid
    M hPA inner).
Qed.

Theorem PA_proves_dynamicTruthQFEx8BranchExclusivityFormula_closed :
  Formula.BProv Formula.Ax_s []
    dynamicTruthQFEx8BranchExclusivityFormula_closed.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact dynamicTruthQFEx8BranchExclusivityFormula_closed_sentence.
  - exact dynamicTruthQFEx8BranchExclusivityFormula_closed_raw_valid.
Qed.

Theorem PA_proves_dynamicTruthQFEx8BranchExclusivityFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthQFEx8BranchExclusivityFormula.
Proof.
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] dynamicTruthQFEx8BranchExclusivityFormula
    (fun n => n)
    PA_proves_dynamicTruthQFEx8BranchExclusivityFormula_closed) as h.
  now rewrite Formula.rename_id in h.
Qed.

(** ------------------------------------------------------------------
    Transparent carrier codes for the two exact implications. *)

Definition rawDynamicTruthSigmaQFRowCode (M : RawPAModel) : M :=
  rawFixedFormulaNumeralCode M dynamicTruthSigmaRowQfFormula.

Definition rawDynamicTruthPiQFRowCode (M : RawPAModel) : M :=
  rawDynamicTruthPiFixedFormulaNumeralCode M
    dynamicTruthPiRowQfFormula.

Definition rawDynamicTruthQFRowBranchExclusivityCode
    (M : RawPAModel) : M :=
  rawFormulaImpCode M (rawDynamicTruthSigmaQFRowCode M)
    (rawFormulaImpCode M (rawDynamicTruthPiQFRowCode M)
      (rawFormulaBotCode M)).

Definition rawDynamicTruthSigmaQFEx8BranchCode
    (M : RawPAModel) : M :=
  rawFormulaEx8Code M (rawDynamicTruthSigmaQFRowCode M).

Definition rawDynamicTruthPiQFEx8BranchCode
    (M : RawPAModel) : M :=
  rawFormulaEx8Code M (rawDynamicTruthPiQFRowCode M).

Definition rawDynamicTruthQFEx8BranchExclusivityCode
    (M : RawPAModel) : M :=
  rawFormulaImpCode M (rawDynamicTruthSigmaQFEx8BranchCode M)
    (rawFormulaImpCode M (rawDynamicTruthPiQFEx8BranchCode M)
      (rawFormulaBotCode M)).

Lemma rawDynamicTruthQFRowBranchExclusivityCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthQFRowBranchExclusivityCode M =
  rawQuotedFormulaCode M
    dynamicTruthQFRowBranchExclusivityFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthQFRowBranchExclusivityCode,
    rawDynamicTruthSigmaQFRowCode,
    rawDynamicTruthPiQFRowCode,
    dynamicTruthQFRowBranchExclusivityFormula.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA).
  rewrite (rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted M hPA).
  reflexivity.
Qed.

Lemma rawDynamicTruthQFEx8BranchExclusivityCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthQFEx8BranchExclusivityCode M =
  rawQuotedFormulaCode M
    dynamicTruthQFEx8BranchExclusivityFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthQFEx8BranchExclusivityCode,
    rawDynamicTruthSigmaQFEx8BranchCode,
    rawDynamicTruthPiQFEx8BranchCode,
    rawDynamicTruthSigmaQFRowCode,
    rawDynamicTruthPiQFRowCode,
    dynamicTruthQFEx8BranchExclusivityFormula,
    dynamicTruthSigmaQFEx8BranchFormula,
    dynamicTruthPiQFEx8BranchFormula,
    fixedLevelEx8.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA).
  rewrite (rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted M hPA).
  reflexivity.
Qed.

Lemma rawDynamicTruthQFRowBranchExclusivityCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthQFRowBranchExclusivityCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthQFRowBranchExclusivityFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthQFRowBranchExclusivityCode_eq_quoted
    by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthQFEx8BranchExclusivityCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthQFEx8BranchExclusivityCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthQFEx8BranchExclusivityFormula).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthQFEx8BranchExclusivityCode_eq_quoted
    by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthSigmaQFEx8BranchCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthSigmaQFEx8BranchCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthSigmaQFEx8BranchFormula).
Proof.
  intros M hPA.
  unfold rawDynamicTruthSigmaQFEx8BranchCode,
    rawDynamicTruthSigmaQFRowCode,
    dynamicTruthSigmaQFEx8BranchFormula, fixedLevelEx8.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA).
  rewrite <- (rawQuotedFormulaCode_standard M hPA).
  reflexivity.
Qed.

Lemma rawDynamicTruthPiQFEx8BranchCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthPiQFEx8BranchCode M =
  rawNumeralValue M
    (formulaCode dynamicTruthPiQFEx8BranchFormula).
Proof.
  intros M hPA.
  unfold rawDynamicTruthPiQFEx8BranchCode,
    rawDynamicTruthPiQFRowCode,
    dynamicTruthPiQFEx8BranchFormula, fixedLevelEx8.
  rewrite (rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted M hPA).
  rewrite <- (rawQuotedFormulaCode_standard M hPA).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Ordinary represented PA proofs of the exact target codes. *)

Theorem raw_codedPAProofOf_dynamicTruthQFRowBranchExclusivity : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthQFRowBranchExclusivityCode M) certificate.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    dynamicTruthQFRowBranchExclusivityFormula
    PA_proves_dynamicTruthQFRowBranchExclusivityFormula)
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthQFRowBranchExclusivityCode_eq_numeral
    by exact hPA.
  exact hcertificate.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthQFEx8BranchExclusivity : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthQFEx8BranchExclusivityCode M) certificate.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    dynamicTruthQFEx8BranchExclusivityFormula
    PA_proves_dynamicTruthQFEx8BranchExclusivityFormula)
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthQFEx8BranchExclusivityCode_eq_numeral
    by exact hPA.
  exact hcertificate.
Qed.

(** ------------------------------------------------------------------
    Local collision in an arbitrary common coded context. *)

Definition rawDynamicTruthQFBranchCollisionRoot (M : RawPAModel)
    (context sigmaBranch piBranch implicationRoot sigmaRoot piRoot : M)
    : M :=
  rawProofImpERoot M context piBranch (rawFormulaBotCode M)
    (rawProofImpERoot M context sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M))
      implicationRoot sigmaRoot)
    piRoot.

Arguments rawDynamicTruthQFBranchCollisionRoot
  M context sigmaBranch piBranch implicationRoot sigmaRoot piRoot
    : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthQFBranchCollision : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context sigmaBranch piBranch implicationRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
    implicationRoot ->
  RawCodedPALocalProofOf M context sigmaBranch sigmaRoot ->
  RawCodedPALocalProofOf M context piBranch piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthQFBranchCollisionRoot M context
      sigmaBranch piBranch implicationRoot sigmaRoot piRoot).
Proof.
  intros M hPA context sigmaBranch piBranch implicationRoot
    sigmaRoot piRoot himp hsigma hpi.
  unfold rawDynamicTruthQFBranchCollisionRoot.
  apply (raw_codedPALocalProofOf_impE M hPA context
    piBranch (rawFormulaBotCode M)); [|exact hpi].
  exact (raw_codedPALocalProofOf_impE M hPA context
    sigmaBranch
    (rawFormulaImpCode M piBranch (rawFormulaBotCode M))
    implicationRoot sigmaRoot himp hsigma).
Qed.

(** Literal specialization of the common-context compiler to the two native
    Ex8 branch codes.  This is the endpoint a later pair of row-disjunction
    eliminators can call once both selected branch proofs share a context. *)
Definition rawDynamicTruthQFEx8BranchCollisionRoot
    (M : RawPAModel)
    (context implicationRoot sigmaRoot piRoot : M) : M :=
  rawDynamicTruthQFBranchCollisionRoot M context
    (rawDynamicTruthSigmaQFEx8BranchCode M)
    (rawDynamicTruthPiQFEx8BranchCode M)
    implicationRoot sigmaRoot piRoot.

Arguments rawDynamicTruthQFEx8BranchCollisionRoot
  M context implicationRoot sigmaRoot piRoot : clear implicits.

Corollary raw_codedPALocalProofOf_dynamicTruthQFEx8BranchCollision : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context implicationRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthQFEx8BranchExclusivityCode M) implicationRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaQFEx8BranchCode M) sigmaRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiQFEx8BranchCode M) piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthQFEx8BranchCollisionRoot M context
      implicationRoot sigmaRoot piRoot).
Proof.
  intros M hPA context implicationRoot sigmaRoot piRoot
    himp hsigma hpi.
  unfold rawDynamicTruthQFEx8BranchCollisionRoot,
    rawDynamicTruthQFEx8BranchExclusivityCode.
  exact (raw_codedPALocalProofOf_dynamicTruthQFBranchCollision
    M hPA context
    (rawDynamicTruthSigmaQFEx8BranchCode M)
    (rawDynamicTruthPiQFEx8BranchCode M)
    implicationRoot sigmaRoot piRoot himp hsigma hpi).
Qed.

(** Guarded insertion into the literal nested branch context.  This theorem
    says exactly what later Ex8 eliminators must supply: a realizable tail
    context and atomically adequate branch codes.  No arbitrary-context
    weakening is hidden in the construction. *)
Theorem raw_dynamicTruthQFBranchCollision_under_assumptions : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context sigmaBranch piBranch implicationRoot,
  RawContextListRealizable M context ->
  RawCodedFormulaAtomicallyAdequate M sigmaBranch ->
  RawCodedFormulaAtomicallyAdequate M piBranch ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
    implicationRoot ->
  exists collisionRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M piBranch
        (rawListNode M sigmaBranch context))
      (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA context sigmaBranch piBranch implicationRoot
    hcontext hsigmaAdequate hpiAdequate himp.
  set (sigmaContext := rawListNode M sigmaBranch context).
  assert (hsigmaContext : RawContextListRealizable M sigmaContext).
  {
    unfold sigmaContext.
    exact (raw_contextList_cons_realizable M hPA
      context sigmaBranch hcontext).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context sigmaBranch
    (rawFormulaImpCode M sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
    implicationRoot hsigmaAdequate hcontext himp)
    as [implicationSigma himpSigma].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    context sigmaBranch hcontext) as hsigmaHead.
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piBranch
    (rawFormulaImpCode M sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
    implicationSigma hpiAdequate hsigmaContext himpSigma)
    as [implicationBoth himpBoth].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piBranch sigmaBranch
    (rawProofAssumptionRoot M sigmaContext sigmaBranch)
    hpiAdequate hsigmaContext hsigmaHead)
    as [sigmaBoth hsigmaBoth].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    sigmaContext piBranch hsigmaContext) as hpiHead.
  exists (rawDynamicTruthQFBranchCollisionRoot M
    (rawListNode M piBranch sigmaContext)
    sigmaBranch piBranch implicationBoth sigmaBoth
    (rawProofAssumptionRoot M
      (rawListNode M piBranch sigmaContext) piBranch)).
  exact (raw_codedPALocalProofOf_dynamicTruthQFBranchCollision
    M hPA (rawListNode M piBranch sigmaContext)
    sigmaBranch piBranch implicationBoth sigmaBoth
    (rawProofAssumptionRoot M
      (rawListNode M piBranch sigmaContext) piBranch)
    himpBoth hsigmaBoth hpiHead).
Qed.

(** Fixed specialization to the genuine native Ex8 QF branch codes. *)
Corollary raw_dynamicTruthQFEx8BranchCollision_under_assumptions : forall
    (M : RawPAModel), RawPASatisfies M -> forall context implicationRoot,
  RawContextListRealizable M context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthQFEx8BranchExclusivityCode M) implicationRoot ->
  exists collisionRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M (rawDynamicTruthPiQFEx8BranchCode M)
        (rawListNode M (rawDynamicTruthSigmaQFEx8BranchCode M)
          context))
      (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA context implicationRoot hcontext himp.
  unfold rawDynamicTruthQFEx8BranchExclusivityCode in himp.
  apply (raw_dynamicTruthQFBranchCollision_under_assumptions
    M hPA context
    (rawDynamicTruthSigmaQFEx8BranchCode M)
    (rawDynamicTruthPiQFEx8BranchCode M)
    implicationRoot hcontext).
  - rewrite rawDynamicTruthSigmaQFEx8BranchCode_eq_numeral
      by exact hPA.
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthSigmaQFEx8BranchFormula).
  - rewrite rawDynamicTruthPiQFEx8BranchCode_eq_numeral
      by exact hPA.
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthPiQFEx8BranchFormula).
  - exact himp.
Qed.

(** Extract the witnessed PA base hidden by the ordinary represented proof.
    This is the exact local form consumed by the guarded branch-context
    compiler above. *)
Theorem raw_dynamicTruthQFEx8BranchExclusivity_local_base : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists witnessList baseContext implicationRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthQFEx8BranchExclusivityCode M) implicationRoot.
Proof.
  intros M hPA.
  destruct (raw_codedPAProofOf_dynamicTruthQFEx8BranchExclusivity
    M hPA) as [certificate hcertificate].
  destruct hcertificate as
    (witnessList & implicationRoot & baseContext &
      _ & hwitness & hcoverage & hendpoint).
  exists witnessList, baseContext, implicationRoot.
  split; [exact hwitness |].
  split; assumption.
Qed.

(** End-to-end native cell: in some honestly witnessed PA base, adjoining
    the two selected Ex8 QF branches produces a checked local contradiction.
    The theorem deliberately does not eliminate the full row disjunctions. *)
Theorem raw_dynamicTruthQFEx8BranchCollision_in_witnessed_base : forall
    (M : RawPAModel), RawPASatisfies M ->
  exists witnessList baseContext collisionRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M
      (rawListNode M (rawDynamicTruthPiQFEx8BranchCode M)
        (rawListNode M (rawDynamicTruthSigmaQFEx8BranchCode M)
          baseContext))
      (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA.
  destruct (raw_dynamicTruthQFEx8BranchExclusivity_local_base M hPA)
    as (witnessList & baseContext & implicationRoot &
      hwitness & himplication).
  assert (hcontext : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitness).
  }
  destruct (raw_dynamicTruthQFEx8BranchCollision_under_assumptions
    M hPA baseContext implicationRoot hcontext himplication)
    as [collisionRoot hcollision].
  exists witnessList, baseContext, collisionRoot.
  split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthQFBranchExclusivity.
