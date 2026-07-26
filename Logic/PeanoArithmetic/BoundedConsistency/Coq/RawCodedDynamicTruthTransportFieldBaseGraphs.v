(**
  Checked level-zero graphs for the cross-level and operation-transport
  coordinates of the dynamic truth master.

  The full carrier-indexed fields are not obtained by putting a
  metatheoretic [nat] into the existing fixed-level definitions: a value of
  an arbitrary raw PA model may be nonstandard.  Their positive branches
  therefore still require genuine model-coded formula and proof compilers.

  At level zero, however, the three intended laws are fixed ordinary PA
  formulas.  This module packages exactly those native formulas through the
  standard output-first quotation graph.  It proves both the graph witness
  expected by the master-base bridge and a coded PA proof targeted at that
  very graph output.  No carrier value is decoded as a Rocq natural.

  The coordinates covered here are, in dependency order:

    2. admissibility-guarded adjacent-level coherence;
    3. invariance under represented formula shift;
    4. invariance under represented single substitution.

  Shift and substitution use the native sealed formulas because their
  displayed Tarski-step formulas have free operation parameters.  The
  coherence formula already universally binds all of its parameters, so its
  exact displayed formula is used directly.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedPAProvability
  RawCodedFixedLevelTruthCoherence
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthOperationTarskiPositive
  RawCodedFixedLevelTruthOperationTarskiSubstitutionPositive
  RawCodedStandardClosedFormulaCodeGraph.

Module PABoundedRawCodedDynamicTruthTransportFieldBaseGraphs.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedFixedLevelTruthCoherence.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiPositive.
Import PABoundedRawCodedFixedLevelTruthOperationTarskiSubstitutionPositive.
Import PABoundedRawCodedStandardClosedFormulaCodeGraph.

(** ------------------------------------------------------------------
    Exact native base formulas and their output-first code graphs. *)

Definition dynamicTruthCrossLevelBaseFieldFormula : formula :=
  fixedLevelAdmissibleTruthCertificateCoherenceFormula 0.

Definition dynamicTruthShiftBaseFieldFormula : formula :=
  fixedLevelFormulaShiftTarskiStepFormula_closed 0.

Definition dynamicTruthSubstitutionBaseFieldFormula : formula :=
  fixedLevelFormulaSubstitutionTarskiStepFormula_closed 0.

Definition dynamicTruthCrossLevelBaseFieldGraph : formula :=
  standardClosedFormulaCodeGraph
    dynamicTruthCrossLevelBaseFieldFormula.

Definition dynamicTruthShiftBaseFieldGraph : formula :=
  standardClosedFormulaCodeGraph
    dynamicTruthShiftBaseFieldFormula.

Definition dynamicTruthSubstitutionBaseFieldGraph : formula :=
  standardClosedFormulaCodeGraph
    dynamicTruthSubstitutionBaseFieldFormula.

(** These are genuine object-language PA derivations of the exact formulas
    selected above.  In particular, no semantic raw-validity premise is
    exported to callers of this module. *)
Theorem PA_proves_dynamicTruthCrossLevelBaseFieldFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthCrossLevelBaseFieldFormula.
Proof.
  unfold dynamicTruthCrossLevelBaseFieldFormula.
  exact
    (PA_proves_fixedLevelAdmissibleTruthCertificateCoherenceFormula 0).
Qed.

Theorem PA_proves_dynamicTruthShiftBaseFieldFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthShiftBaseFieldFormula.
Proof.
  unfold dynamicTruthShiftBaseFieldFormula.
  exact (PA_proves_fixedLevelFormulaShiftTarskiStepFormula_closed 0).
Qed.

Theorem PA_proves_dynamicTruthSubstitutionBaseFieldFormula :
  Formula.BProv Formula.Ax_s []
    dynamicTruthSubstitutionBaseFieldFormula.
Proof.
  unfold dynamicTruthSubstitutionBaseFieldFormula.
  exact
    (PA_proves_fixedLevelFormulaSubstitutionTarskiStepFormula_closed 0).
Qed.

(** ------------------------------------------------------------------
    Exact zero views.

    Each graph is functional at zero: a satisfying output is precisely the
    structural quotation of its advertised native field formula. *)

Theorem dynamicTruthCrossLevelBaseFieldGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail output,
  raw_formula_sat M
    (scons M output (scons M (raw_zero M) tail))
    dynamicTruthCrossLevelBaseFieldGraph <->
  output = rawQuotedFormulaCode M
    dynamicTruthCrossLevelBaseFieldFormula.
Proof.
  intros M hPA tail output.
  unfold dynamicTruthCrossLevelBaseFieldGraph.
  exact (standardClosedFormulaCodeGraph_zero_iff M hPA
    dynamicTruthCrossLevelBaseFieldFormula tail output).
Qed.

Theorem dynamicTruthShiftBaseFieldGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail output,
  raw_formula_sat M
    (scons M output (scons M (raw_zero M) tail))
    dynamicTruthShiftBaseFieldGraph <->
  output = rawQuotedFormulaCode M dynamicTruthShiftBaseFieldFormula.
Proof.
  intros M hPA tail output.
  unfold dynamicTruthShiftBaseFieldGraph.
  exact (standardClosedFormulaCodeGraph_zero_iff M hPA
    dynamicTruthShiftBaseFieldFormula tail output).
Qed.

Theorem dynamicTruthSubstitutionBaseFieldGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail output,
  raw_formula_sat M
    (scons M output (scons M (raw_zero M) tail))
    dynamicTruthSubstitutionBaseFieldGraph <->
  output = rawQuotedFormulaCode M
    dynamicTruthSubstitutionBaseFieldFormula.
Proof.
  intros M hPA tail output.
  unfold dynamicTruthSubstitutionBaseFieldGraph.
  exact (standardClosedFormulaCodeGraph_zero_iff M hPA
    dynamicTruthSubstitutionBaseFieldFormula tail output).
Qed.

(** The standard-witness form is the exact interface consumed by
    [RawSixFieldMasterZeroBProvComponentPackage]. *)
Theorem dynamicTruthCrossLevelBaseFieldGraph_standard_zero_witness : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall tail : nat -> M,
    raw_formula_sat M
      (scons M
        (rawQuotedFormulaCode M dynamicTruthCrossLevelBaseFieldFormula)
        (scons M (raw_zero M) tail))
      dynamicTruthCrossLevelBaseFieldGraph.
Proof.
  intros M hPA tail.
  unfold dynamicTruthCrossLevelBaseFieldGraph.
  exact (standardClosedFormulaCodeGraph_zero M hPA
    dynamicTruthCrossLevelBaseFieldFormula tail).
Qed.

Theorem dynamicTruthShiftBaseFieldGraph_standard_zero_witness : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall tail : nat -> M,
    raw_formula_sat M
      (scons M
        (rawQuotedFormulaCode M dynamicTruthShiftBaseFieldFormula)
        (scons M (raw_zero M) tail))
      dynamicTruthShiftBaseFieldGraph.
Proof.
  intros M hPA tail.
  unfold dynamicTruthShiftBaseFieldGraph.
  exact (standardClosedFormulaCodeGraph_zero M hPA
    dynamicTruthShiftBaseFieldFormula tail).
Qed.

Theorem
    dynamicTruthSubstitutionBaseFieldGraph_standard_zero_witness : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall tail : nat -> M,
    raw_formula_sat M
      (scons M
        (rawQuotedFormulaCode M dynamicTruthSubstitutionBaseFieldFormula)
        (scons M (raw_zero M) tail))
      dynamicTruthSubstitutionBaseFieldGraph.
Proof.
  intros M hPA tail.
  unfold dynamicTruthSubstitutionBaseFieldGraph.
  exact (standardClosedFormulaCodeGraph_zero M hPA
    dynamicTruthSubstitutionBaseFieldFormula tail).
Qed.

(** ------------------------------------------------------------------
    Proof-producing zero slices.

    These results pin the raw proof target to the same output selected by the
    corresponding graph.  They are intentionally stated at zero even though
    the generic fixed graph ignores its level input: only the zero branch is
    part of the dynamic field represented here. *)

Theorem raw_dynamicTruthCrossLevelBaseFieldGraph_proof : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  exists output certificate : M,
    raw_formula_sat M
      (scons M output (scons M (raw_zero M) tail))
      dynamicTruthCrossLevelBaseFieldGraph /\
    RawCodedPAProofOf M output certificate.
Proof.
  intros M hPA tail.
  unfold dynamicTruthCrossLevelBaseFieldGraph.
  exact (raw_standardClosedFormulaCodeGraph_proof_of_BProv
    M hPA dynamicTruthCrossLevelBaseFieldFormula
    PA_proves_dynamicTruthCrossLevelBaseFieldFormula
    tail (raw_zero M)).
Qed.

Theorem raw_dynamicTruthShiftBaseFieldGraph_proof : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  exists output certificate : M,
    raw_formula_sat M
      (scons M output (scons M (raw_zero M) tail))
      dynamicTruthShiftBaseFieldGraph /\
    RawCodedPAProofOf M output certificate.
Proof.
  intros M hPA tail.
  unfold dynamicTruthShiftBaseFieldGraph.
  exact (raw_standardClosedFormulaCodeGraph_proof_of_BProv
    M hPA dynamicTruthShiftBaseFieldFormula
    PA_proves_dynamicTruthShiftBaseFieldFormula
    tail (raw_zero M)).
Qed.

Theorem raw_dynamicTruthSubstitutionBaseFieldGraph_proof : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  exists output certificate : M,
    raw_formula_sat M
      (scons M output (scons M (raw_zero M) tail))
      dynamicTruthSubstitutionBaseFieldGraph /\
    RawCodedPAProofOf M output certificate.
Proof.
  intros M hPA tail.
  unfold dynamicTruthSubstitutionBaseFieldGraph.
  exact (raw_standardClosedFormulaCodeGraph_proof_of_BProv
    M hPA dynamicTruthSubstitutionBaseFieldFormula
    PA_proves_dynamicTruthSubstitutionBaseFieldFormula
    tail (raw_zero M)).
Qed.

End PABoundedRawCodedDynamicTruthTransportFieldBaseGraphs.
