(**
  The exact level-zero graph for the PA-axiom-soundness coordinate.

  The graph input is the dynamic certificate index.  At index zero the
  next truth predicate is still ordinary fixed syntax, so this coordinate
  can be an ordinary closed PA formula.  The formula below is the direct
  counterpart of Lean's [standardBaseSuccessorAxiomSoundnessSentence]: a
  code recognized by the represented PA-axiom relation and lying in the
  base admissible domain has a level-one Sigma truth certificate.

  There are two representation differences worth making explicit.

  - Coq's transparent PA recognizer exposes a witness.  Existentially
    hiding that witness gives the unary recognized-axiom predicate used in
    the displayed sentence.
  - The established Coq PA-axiom truth theorem is stated under the total
    zero beta assignment.  This is the assignment used by restricted-proof
    exclusion for closed PA axioms.  Its two beta parameters therefore
    appear as literal zeroes, rather than as Lean's single HFS sequence
    parameter.

  The proof is not a placeholder tautology.  Its induction-witness branch
  uses [raw_fixedLevelPAAxiomInductionSigmaSound_all], whose proof performs
  PA-definable induction on arbitrary, possibly nonstandard source codes.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedRestrictedPAConsistency
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedPAProvability
  RawCodedPAAxiomWitness
  RawCodedPAAxiomTruth
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedStandardClosedFormulaCodeGraph.

Module PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.

Import ListNotations.
Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedRestrictedPAConsistency.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomTruth.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedStandardClosedFormulaCodeGraph.

(** Existential closure of the transparent PA-axiom witness relation. *)
Definition witnessedPAAxiomRecognitionTermAt (axiom : term) : formula :=
  pEx
    (codedPAAxiomWitnessTermAt
      (tVar 0) (liftTerm 1 axiom)).

Definition RawWitnessedPAAxiomRecognition
    (M : RawPAModel) (axiom : M) : Prop :=
  exists witness : M, RawCodedPAAxiomWitness M witness axiom.

Arguments RawWitnessedPAAxiomRecognition M axiom : clear implicits.

Lemma raw_sat_witnessedPAAxiomRecognitionTermAt_iff : forall
    (M : RawPAModel) e axiom,
  raw_formula_sat M e (witnessedPAAxiomRecognitionTermAt axiom) <->
  RawWitnessedPAAxiomRecognition M (raw_term_eval M e axiom).
Proof.
  intros M e axiom.
  unfold witnessedPAAxiomRecognitionTermAt,
    RawWitnessedPAAxiomRecognition.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedPAAxiomWitnessTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The one-free-variable implication before universal closure.

    Coq indexes [RawFixedLevelTruthAdmissible] by the *input* level.  Thus
    the first transition has input level 0 and successor certificate level
    1.  This is the same base transition whose ordinary Lean presentation
    displays the numeral one in its quantifier-bound code while its dynamic
    lower index remains zero.

    [RawFixedLevelTruthAdmissible] spells out the Coq representation of the
    bounded-domain side condition: honest atomic syntax, a defined beta
    assignment, and membership in one of the two base domains. *)
Definition dynamicTruthAxiomSoundnessBaseBodyFormula : formula :=
  pImp
    (pAnd
      (witnessedPAAxiomRecognitionTermAt (tVar 0))
      (fixedLevelTruthAdmissibleTermAt
        0 (tVar 0) tZero tZero))
    (fixedLevelSigmaTruthCertificateTermAt
      1 (tVar 0) tZero tZero).

Definition RawDynamicTruthAxiomSoundnessBaseAt (M : RawPAModel) : Prop :=
  forall axiom : M,
    RawWitnessedPAAxiomRecognition M axiom ->
    RawFixedLevelTruthAdmissible M 0 axiom
      (raw_zero M) (raw_zero M) ->
    RawFixedLevelSigmaTruthCertificate M 1 axiom
      (raw_zero M) (raw_zero M).

Arguments RawDynamicTruthAxiomSoundnessBaseAt M : clear implicits.

Lemma raw_sat_dynamicTruthAxiomSoundnessBaseBodyFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthAxiomSoundnessBaseBodyFormula <->
  (RawWitnessedPAAxiomRecognition M (e 0) ->
   RawFixedLevelTruthAdmissible M 0 (e 0)
     (raw_zero M) (raw_zero M) ->
   RawFixedLevelSigmaTruthCertificate M 1 (e 0)
     (raw_zero M) (raw_zero M)).
Proof.
  intros M e.
  unfold dynamicTruthAxiomSoundnessBaseBodyFormula.
  cbn [raw_formula_sat].
  rewrite raw_sat_witnessedPAAxiomRecognitionTermAt_iff,
    raw_sat_fixedLevelTruthAdmissibleTermAt_iff,
    raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  cbn [raw_term_eval]. tauto.
Qed.

(** Universal closure of the one-parameter body.  Using the library's
    structural closure operator avoids unfolding the very large recursive
    fixed-truth formula merely to prove that the result is a sentence.  The
    exact semantic theorem below shows that the closure quantifies precisely
    the intended axiom code and introduces no semantic strengthening. *)
Definition dynamicTruthAxiomSoundnessBaseFieldFormula : formula :=
  Formula.sealPA dynamicTruthAxiomSoundnessBaseBodyFormula.

Theorem raw_sat_dynamicTruthAxiomSoundnessBaseFieldFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthAxiomSoundnessBaseFieldFormula <->
  RawDynamicTruthAxiomSoundnessBaseAt M.
Proof.
  intros M e.
  unfold dynamicTruthAxiomSoundnessBaseFieldFormula.
  rewrite raw_formula_sat_sealPA_iff_valid.
  unfold RawDynamicTruthAxiomSoundnessBaseAt.
  split.
  - intros hvalid axiom hrecognized hadmissible.
    pose proof (proj1
      (raw_sat_dynamicTruthAxiomSoundnessBaseBodyFormula_iff M
        (scons M axiom e))
      (hvalid (scons M axiom e))) as hbody.
    cbn [scons] in hbody.
    exact (hbody hrecognized hadmissible).
  - intros hlaw e'.
    apply (proj2
      (raw_sat_dynamicTruthAxiomSoundnessBaseBodyFormula_iff M e')).
    exact (hlaw (e' 0)).
Qed.

Theorem dynamicTruthAxiomSoundnessBaseFieldFormula_sentence :
  Formula.Sentence dynamicTruthAxiomSoundnessBaseFieldFormula.
Proof.
  unfold dynamicTruthAxiomSoundnessBaseFieldFormula.
  apply Formula.sealPA_sentence.
Qed.

(** Fixed-level PA-axiom truth discharges the exact semantic law.  The
    existential recognizer supplies the transparent witness consumed by
    [raw_codedPAAxiomWitness_sigma_zero]; the nonstandard induction branch
    is supplied by the unconditional shift-adequacy theorem. *)
Theorem raw_dynamicTruthAxiomSoundnessBase_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthAxiomSoundnessBaseAt M.
Proof.
  intros M hPA axiom [witness hwitness] hadmissible.
  exact (raw_codedPAAxiomWitness_sigma_zero M hPA 0
    (raw_fixedLevelPAAxiomInductionSigmaSound_all M hPA 0)
    witness axiom hwitness hadmissible).
Qed.

Theorem dynamicTruthAxiomSoundnessBaseFieldFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e dynamicTruthAxiomSoundnessBaseFieldFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_dynamicTruthAxiomSoundnessBaseFieldFormula_iff M e)).
  exact (raw_dynamicTruthAxiomSoundnessBase_all M hPA).
Qed.

(** Arithmetic completeness produces an actual [BProv] derivation of this
    exact non-tautological sentence. *)
Theorem PA_proves_dynamicTruthAxiomSoundnessBaseFieldFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthAxiomSoundnessBaseFieldFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact dynamicTruthAxiomSoundnessBaseFieldFormula_sentence.
  - exact dynamicTruthAxiomSoundnessBaseFieldFormula_raw_valid.
Qed.

(** ------------------------------------------------------------------
    Output-first graph and the interfaces consumed by the six-field base
    package. *)

Definition dynamicTruthAxiomSoundnessBaseFieldGraph : formula :=
  standardClosedFormulaCodeGraph
    dynamicTruthAxiomSoundnessBaseFieldFormula.

Theorem dynamicTruthAxiomSoundnessBaseFieldGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail output,
  raw_formula_sat M
    (scons M output (scons M (raw_zero M) tail))
    dynamicTruthAxiomSoundnessBaseFieldGraph <->
  output = rawQuotedFormulaCode M
    dynamicTruthAxiomSoundnessBaseFieldFormula.
Proof.
  intros M hPA tail output.
  unfold dynamicTruthAxiomSoundnessBaseFieldGraph.
  exact (standardClosedFormulaCodeGraph_zero_iff M hPA
    dynamicTruthAxiomSoundnessBaseFieldFormula tail output).
Qed.

Theorem
    dynamicTruthAxiomSoundnessBaseFieldGraph_standard_zero_witness : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail : nat -> M,
  raw_formula_sat M
    (scons M
      (rawQuotedFormulaCode M
        dynamicTruthAxiomSoundnessBaseFieldFormula)
      (scons M (raw_zero M) tail))
    dynamicTruthAxiomSoundnessBaseFieldGraph.
Proof.
  intros M hPA tail.
  unfold dynamicTruthAxiomSoundnessBaseFieldGraph.
  exact (standardClosedFormulaCodeGraph_zero M hPA
    dynamicTruthAxiomSoundnessBaseFieldFormula tail).
Qed.

(** The proof target is definitionally the same quoted output selected by
    the graph.  This is the exact witness needed either directly or through
    [RawSixFieldMasterZeroBProvComponentPackage]. *)
Theorem raw_dynamicTruthAxiomSoundnessBaseFieldGraph_proof : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  exists output certificate : M,
    raw_formula_sat M
      (scons M output (scons M (raw_zero M) tail))
      dynamicTruthAxiomSoundnessBaseFieldGraph /\
    RawCodedPAProofOf M output certificate.
Proof.
  intros M hPA tail.
  unfold dynamicTruthAxiomSoundnessBaseFieldGraph.
  exact (raw_standardClosedFormulaCodeGraph_proof_of_BProv
    M hPA dynamicTruthAxiomSoundnessBaseFieldFormula
    PA_proves_dynamicTruthAxiomSoundnessBaseFieldFormula
    tail (raw_zero M)).
Qed.

End PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.
