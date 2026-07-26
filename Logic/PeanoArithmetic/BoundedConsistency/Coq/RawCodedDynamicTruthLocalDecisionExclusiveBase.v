(**
  The proof-producing zero slice of the dynamic local truth field.

  The native fixed-level development exposes two closed PA theorems which
  form the decision/exclusivity core of a local Tarski package:

  - every admissible input is accepted by one of the two successor
    polarities; and
  - the two successor polarities cannot both accept an admissible input.

  Their proofs use the construction, elimination, schedule, and truth-law
  layers respectively.  At external input level zero, both formulae are
  standard syntax.  We can therefore conjoin their ordinary [BProv]
  derivations, quote the exact conjunction code, and obtain a genuine
  [RawCodedPAProofOf] certificate in every raw PA model.

  This file intentionally stops at that honest boundary.  It does not call
  this two-law core the complete Lean-style augmented local field, and it
  does not manufacture a nonstandard-level proof from semantic validity.
  The positive branch still needs a represented proof-template compiler
  whose target is built from the carrier-coded global Sigma/Pi predicates.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruthLaws
  RawCodedFixedLevelTruthScheduleInvariant
  RawCodedFixedLevelTruthSchedule
  RawCodedSyntaxConstructors
  RawCodedPAProvability
  RawCodedDynamicLocalFieldGraph
  RawCodedStandardClosedFormulaCodeGraph.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedFixedLevelTruthScheduleInvariant.
Import PABoundedRawCodedFixedLevelTruthSchedule.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicLocalFieldGraph.
Import PABoundedRawCodedStandardClosedFormulaCodeGraph.

(** The two native local laws in a stable right-associated field shape. *)
Definition fixedLevelLocalDecisionExclusiveBundleFormula
    (inputLevel : nat) : formula :=
  pAnd
    (fixedLevelInputTruthCertificateTotalityFormula inputLevel)
    (fixedLevelAdmissibleTruthCertificateExclusiveFormula inputLevel).

Definition RawFixedLevelLocalDecisionExclusiveBundleAt
    (M : RawPAModel) (inputLevel : nat) : Prop :=
  RawFixedLevelInputTruthCertificateTotalityAt M inputLevel /\
  RawFixedLevelAdmissibleTruthCertificateExclusiveAt M inputLevel.

Arguments RawFixedLevelLocalDecisionExclusiveBundleAt M inputLevel
  : clear implicits.

(** Exact arbitrary-model semantics of the displayed conjunction. *)
Theorem raw_sat_fixedLevelLocalDecisionExclusiveBundleFormula_iff : forall
    (M : RawPAModel) e inputLevel,
  raw_formula_sat M e
    (fixedLevelLocalDecisionExclusiveBundleFormula inputLevel) <->
  RawFixedLevelLocalDecisionExclusiveBundleAt M inputLevel.
Proof.
  intros M e inputLevel.
  unfold fixedLevelLocalDecisionExclusiveBundleFormula,
    RawFixedLevelLocalDecisionExclusiveBundleAt.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelInputTruthCertificateTotalityFormula_iff.
  rewrite raw_sat_fixedLevelAdmissibleTruthCertificateExclusiveFormula_iff.
  reflexivity.
Qed.

(** The core is an actual PA theorem at every external input level.  This is
    useful for standard-point checks, but it is not a compiler at a carrier
    element of a nonstandard model. *)
Theorem PA_proves_fixedLevelLocalDecisionExclusiveBundleFormula : forall
    inputLevel,
  Formula.BProv Formula.Ax_s []
    (fixedLevelLocalDecisionExclusiveBundleFormula inputLevel).
Proof.
  intro inputLevel.
  unfold fixedLevelLocalDecisionExclusiveBundleFormula.
  exact (Formula.BProv_andI Formula.Ax_s []
    (fixedLevelInputTruthCertificateTotalityFormula inputLevel)
    (fixedLevelAdmissibleTruthCertificateExclusiveFormula inputLevel)
    (PA_proves_fixedLevelInputTruthCertificateTotalityFormula inputLevel)
    (PA_proves_fixedLevelAdmissibleTruthCertificateExclusiveFormula
      inputLevel)).
Qed.

(** The standard zero field used by the master package's base callback. *)
Definition dynamicTruthLocalDecisionExclusiveBaseFormula : formula :=
  fixedLevelLocalDecisionExclusiveBundleFormula 0.

Definition dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph : formula :=
  standardClosedFormulaCodeGraph
    dynamicTruthLocalDecisionExclusiveBaseFormula.

Theorem dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph_representation
    : forall (M : RawPAModel), RawPASatisfies M -> forall tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph <->
  output = rawQuotedFormulaCode M
    dynamicTruthLocalDecisionExclusiveBaseFormula.
Proof.
  intros M hPA tail level output.
  unfold dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph.
  exact (standardClosedFormulaCodeGraph_representation M hPA
    dynamicTruthLocalDecisionExclusiveBaseFormula tail level output).
Qed.

(** Exact component-totality interface for the base half of
    [dynamicLocalFieldGraph]. *)
Theorem dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph_raw_total :
    forall (M : RawPAModel),
  RawDynamicLocalBaseGraphTotal M
    dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph.
Proof.
  intros M.
  unfold dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph.
  exact (standardClosedFormulaCodeGraph_dynamic_base_total M
    dynamicTruthLocalDecisionExclusiveBaseFormula).
Qed.

(** More importantly, the selected zero output is accompanied by an
    ordinary represented PA proof of that exact output code. *)
Theorem
    raw_dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph_provable :
    forall (M : RawPAModel), RawPASatisfies M -> forall tail,
  exists output certificate : M,
    raw_formula_sat M
      (scons M output (scons M (raw_zero M) tail))
      dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph /\
    RawCodedPAProofOf M output certificate.
Proof.
  intros M hPA tail.
  unfold dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph.
  exact (raw_standardClosedFormulaCodeGraph_proof_of_BProv M hPA
    dynamicTruthLocalDecisionExclusiveBaseFormula
    (PA_proves_fixedLevelLocalDecisionExclusiveBundleFormula 0)
    tail (raw_zero M)).
Qed.

End PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.
