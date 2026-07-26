(**
  The proof-safe graph boundary for the dynamic local truth field.

  A concrete local-law transform is read under

      fieldCode :: globalSigmaCode :: globalPiCode :: level :: tail.

  This module composes that transform with the *paired* global truth-code
  orbit and exposes the master assembler's ordinary convention

      fieldCode :: level :: tail.

  The public construction is intentionally parametric in the transform.  A
  suitable transform must both construct the desired local-law bundle code
  and return an ordinary represented PA proof targeted at that exact code.
  This names the remaining nonstandard proof-template obligation without
  weakening it to graph totality or semantic validity.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedOutputFirstPairedFormulaGraphComposition.

Module PABoundedRawCodedDynamicTruthLocalProofFieldGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedOutputFirstPairedFormulaGraphComposition.

Definition dynamicTruthLocalProofFieldGraph
    (localLawTransformGraph : formula) : formula :=
  outputFirstPairedFormulaGraphComposition
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph
    localLawTransformGraph.

Definition RawDynamicTruthLocalProofFieldGraphAt
    (M : RawPAModel) (localLawTransformGraph : formula)
    (tail : nat -> M) (level fieldCode : M) : Prop :=
  exists globalSigmaCode globalPiCode : M,
    raw_formula_sat M
      (scons M globalSigmaCode
        (scons M globalPiCode (scons M level tail)))
      dynamicTruthPairedGlobalFormulaCodeOrbitGraph /\
    raw_formula_sat M
      (scons M fieldCode
        (scons M globalSigmaCode
          (scons M globalPiCode (scons M level tail))))
      localLawTransformGraph.

Arguments RawDynamicTruthLocalProofFieldGraphAt
  M localLawTransformGraph tail level fieldCode : clear implicits.

Theorem raw_sat_dynamicTruthLocalProofFieldGraph_iff : forall
    (M : RawPAModel) localLawTransformGraph tail level fieldCode,
  raw_formula_sat M
    (scons M fieldCode (scons M level tail))
    (dynamicTruthLocalProofFieldGraph localLawTransformGraph) <->
  RawDynamicTruthLocalProofFieldGraphAt M
    localLawTransformGraph tail level fieldCode.
Proof.
  intros M localLawTransformGraph tail level fieldCode.
  unfold dynamicTruthLocalProofFieldGraph,
    RawDynamicTruthLocalProofFieldGraphAt.
  rewrite raw_sat_outputFirstPairedFormulaGraphComposition_iff.
  unfold RawOutputFirstPairedFormulaGraphCompositionAt.
  reflexivity.
Qed.

(** This is the exact remaining positive-field interface.  In particular,
    the conclusion is not merely that the displayed law code is true in
    [M]: it contains a checked ordinary PA proof certificate for that code. *)
Definition RawDynamicTruthLocalLawTransformProofTotal
    (M : RawPAModel) (localLawTransformGraph : formula) : Prop :=
  RawOutputFirstPairedFormulaTransformProofTotal M
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph
    localLawTransformGraph.

Arguments RawDynamicTruthLocalLawTransformProofTotal
  M localLawTransformGraph : clear implicits.

Theorem dynamicTruthLocalProofFieldGraph_raw_proof_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall localLawTransformGraph,
  RawDynamicTruthLocalLawTransformProofTotal M localLawTransformGraph ->
  forall (tail : nat -> M) level,
    exists fieldCode certificate : M,
      raw_formula_sat M
        (scons M fieldCode (scons M level tail))
        (dynamicTruthLocalProofFieldGraph localLawTransformGraph) /\
      RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA localLawTransformGraph htransform.
  apply (outputFirstPairedFormulaGraphComposition_raw_proof_total M
    dynamicTruthPairedGlobalFormulaCodeOrbitGraph
    localLawTransformGraph).
  - intros tail level.
    destruct
      (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
        M hPA tail level) as
      (globalSigmaCode & globalPiCode & horbit & _ & _).
    exists globalSigmaCode, globalPiCode. exact horbit.
  - exact htransform.
Qed.

End PABoundedRawCodedDynamicTruthLocalProofFieldGraph.
