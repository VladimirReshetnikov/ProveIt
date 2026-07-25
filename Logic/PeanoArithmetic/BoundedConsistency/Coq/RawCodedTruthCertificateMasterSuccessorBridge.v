(**
  Component-level construction of the concrete master-package successor.

  A current direct package contains a graph-selected master code and an
  ordinary coded PA proof of that same code.  A successor compiler may inspect
  that concrete graph assertion and its exact certificate, but must return:

  - six witnesses accepted by the five field graphs and the compact target
    graph at the successor level; and
  - either six local proofs in one witnessed PA-axiom context, or an ordinary
    proof already targeted at the transparent master code of those witnesses.

  These interfaces expose the actual component obligations.  In particular,
  neither one assumes [RawSixFieldMasterPackageSuccessor] under another name,
  and neither permits a proof target unrelated to the selected graph outputs.
  There is intentionally no [BProv] successor route: a carrier [level] can be
  nonstandard, so no metatheoretic formula indexed by it is available to
  quote.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedRestrictedPAConsistencyFormulaCode
  CompactRestrictedPAConsistencyFormulaCodeGraph
  RawCodedTruthCertificateFinalProjection
  RawCodedTruthCertificateMasterGraph
  RawCodedTruthCertificateMasterInduction
  RawCodedTruthCertificateMasterAssembler
  RawCodedTruthCertificateMasterIntroduction
  RawCodedTruthCertificateMasterBaseBridge.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterSuccessorBridge.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedRawCodedTruthCertificateFinalProjection.
Import PABoundedRawCodedTruthCertificateMasterGraph.
Import PABoundedRawCodedTruthCertificateMasterInduction.
Import PABoundedRawCodedTruthCertificateMasterAssembler.
Import PABoundedRawCodedTruthCertificateMasterIntroduction.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.

(** The six concrete graph witnesses at an arbitrary carrier level.  Unlike
    the base bridge's zero-only specialization, this relation is suitable for
    both the current and successor levels of a nonstandard PA model. *)
Definition RawSixFieldMasterGraphWitnessesAt (M : RawPAModel)
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    (tail : nat -> M) (level : M)
    (field1 field2 field3 field4 field5 finalField : M) : Prop :=
  raw_formula_sat M
    (scons M field1 (scons M level tail)) field1Graph /\
  raw_formula_sat M
    (scons M field2 (scons M level tail)) field2Graph /\
  raw_formula_sat M
    (scons M field3 (scons M level tail)) field3Graph /\
  raw_formula_sat M
    (scons M field4 (scons M level tail)) field4Graph /\
  raw_formula_sat M
    (scons M field5 (scons M level tail)) field5Graph /\
  raw_formula_sat M
    (scons M finalField (scons M level tail))
    compactRestrictedPAConsistencyFormulaCodeGraph.

Arguments RawSixFieldMasterGraphWitnessesAt
  M field1Graph field2Graph field3Graph field4Graph field5Graph tail level
    field1 field2 field3 field4 field5 finalField : clear implicits.

(** An already packaged proof is useful only when its target is fixed to the
    transparent master code of the six supplied witnesses. *)
Definition RawSixFieldMasterExactProofOf (M : RawPAModel)
    (field1 field2 field3 field4 field5 finalField : M) : Prop :=
  exists certificate : M,
    RawCodedPAProofOf M
      (rawSixFieldMasterCode M
        field1 field2 field3 field4 field5 finalField)
      certificate.

Arguments RawSixFieldMasterExactProofOf
  M field1 field2 field3 field4 field5 finalField : clear implicits.

(** Graph witnesses and an exact ordinary proof form the represented direct
    package.  This small assembly lemma is shared by both successor routes. *)
Lemma raw_sixFieldMasterDirectPackage_of_components : forall
    (M : RawPAModel)
      field1Graph field2Graph field3Graph field4Graph field5Graph
      tail level field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterGraphWitnessesAt M
    field1Graph field2Graph field3Graph field4Graph field5Graph
    tail level field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterExactProofOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterDirectPackageAt M
    (concreteSixFieldMasterGraph
      field1Graph field2Graph field3Graph field4Graph field5Graph)
    tail level.
Proof.
  intros M field1Graph field2Graph field3Graph field4Graph field5Graph
    tail level field1 field2 field3 field4 field5 finalField
    hgraphs [certificate hcertificate].
  set (master := rawSixFieldMasterCode M
    field1 field2 field3 field4 field5 finalField).
  exists master, certificate. split.
  - apply (proj2 (raw_sat_concreteSixFieldMasterGraph_iff M
      field1Graph field2Graph field3Graph field4Graph field5Graph
      tail level master)).
    unfold RawSixFieldMasterGraphWitnessesAt in hgraphs.
    destruct hgraphs as
      (hfield1Graph & hfield2Graph & hfield3Graph & hfield4Graph &
        hfield5Graph & hfinalGraph).
    exists field1, field2, field3, field4, field5, finalField.
    repeat split.
    + exact hfield1Graph.
    + exact hfield2Graph.
    + exact hfield3Graph.
    + exact hfield4Graph.
    + exact hfield5Graph.
    + exact (proj1
        (compactRestrictedPAConsistencyFormulaCodeGraph_representation
          M tail level finalField) hfinalGraph).
  - unfold master. exact hcertificate.
Qed.

(** Six common-context local proofs package into an ordinary proof of exactly
    the corresponding transparent master code. *)
Lemma raw_sixFieldMasterExactProofOf_of_common_context : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1 field2 field3 field4 field5 finalField,
  RawSixFieldMasterCommonContextProofsOf M
    field1 field2 field3 field4 field5 finalField ->
  RawSixFieldMasterExactProofOf M
    field1 field2 field3 field4 field5 finalField.
Proof.
  intros M hPA field1 field2 field3 field4 field5 finalField hproofs.
  unfold RawSixFieldMasterCommonContextProofsOf in hproofs.
  destruct hproofs as
    (witnessList & context & root1 & root2 & root3 & root4 & root5 &
      finalRoot & hwitness & hfield1Proof & hfield2Proof &
      hfield3Proof & hfield4Proof & hfield5Proof & hfinalProof).
  exact (raw_codedPAProofOf_sixFieldMaster_intro M hPA
    witnessList context
    field1 field2 field3 field4 field5 finalField
    root1 root2 root3 root4 root5 finalRoot
    hwitness hfield1Proof hfield2Proof hfield3Proof
    hfield4Proof hfield5Proof hfinalProof).
Qed.

(** A nonstandard-safe component successor.  Its first two premises are
    precisely the unpacked current direct package.  Its conclusion is more
    structured than the package callback: it must expose all six next graph
    witnesses and six proofs in one common witnessed-axiom context. *)
Definition RawSixFieldMasterRawComponentSuccessor (M : RawPAModel)
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    : Prop :=
  forall (tail : nat -> M) level currentMaster currentCertificate,
    raw_formula_sat M
      (scons M currentMaster (scons M level tail))
      (concreteSixFieldMasterGraph
        field1Graph field2Graph field3Graph field4Graph field5Graph) ->
    RawCodedPAProofOf M currentMaster currentCertificate ->
    exists nextField1 nextField2 nextField3 nextField4 nextField5
        nextFinalField : M,
      RawSixFieldMasterGraphWitnessesAt M
        field1Graph field2Graph field3Graph field4Graph field5Graph
        tail (raw_succ M level)
        nextField1 nextField2 nextField3 nextField4 nextField5
        nextFinalField /\
      RawSixFieldMasterCommonContextProofsOf M
        nextField1 nextField2 nextField3 nextField4 nextField5
        nextFinalField.

Arguments RawSixFieldMasterRawComponentSuccessor
  M field1Graph field2Graph field3Graph field4Graph field5Graph
    : clear implicits.

(** A variant for successor compilers which already produce one ordinary
    proof.  Requiring [RawSixFieldMasterExactProofOf] is strictly more
    informative than an unindexed certificate and prevents target drift. *)
Definition RawSixFieldMasterExactProofComponentSuccessor (M : RawPAModel)
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    : Prop :=
  forall (tail : nat -> M) level currentMaster currentCertificate,
    raw_formula_sat M
      (scons M currentMaster (scons M level tail))
      (concreteSixFieldMasterGraph
        field1Graph field2Graph field3Graph field4Graph field5Graph) ->
    RawCodedPAProofOf M currentMaster currentCertificate ->
    exists nextField1 nextField2 nextField3 nextField4 nextField5
        nextFinalField : M,
      RawSixFieldMasterGraphWitnessesAt M
        field1Graph field2Graph field3Graph field4Graph field5Graph
        tail (raw_succ M level)
        nextField1 nextField2 nextField3 nextField4 nextField5
        nextFinalField /\
      RawSixFieldMasterExactProofOf M
        nextField1 nextField2 nextField3 nextField4 nextField5
        nextFinalField.

Arguments RawSixFieldMasterExactProofComponentSuccessor
  M field1Graph field2Graph field3Graph field4Graph field5Graph
    : clear implicits.

(** A raw common-context successor compiler implies the concrete successor
    callback.  The current direct package is unpacked into its graph assertion
    and exact proof, after which the returned next components are assembled
    with the two lemmas above. *)
Theorem raw_sixFieldMasterPackageSuccessor_of_raw_components : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1Graph field2Graph field3Graph field4Graph field5Graph,
  RawSixFieldMasterRawComponentSuccessor M
    field1Graph field2Graph field3Graph field4Graph field5Graph ->
  RawSixFieldMasterPackageSuccessor M
    (concreteSixFieldMasterGraph
      field1Graph field2Graph field3Graph field4Graph field5Graph).
Proof.
  intros M hPA
    field1Graph field2Graph field3Graph field4Graph field5Graph
    hsuccessor tail level hcurrent.
  destruct hcurrent as
    (currentMaster & currentCertificate & hcurrentGraph & hcurrentProof).
  destruct (hsuccessor tail level currentMaster currentCertificate
    hcurrentGraph hcurrentProof) as
    (nextField1 & nextField2 & nextField3 & nextField4 & nextField5 &
      nextFinalField & hnextGraphs & hnextProofs).
  apply (raw_sixFieldMasterDirectPackage_of_components M
    field1Graph field2Graph field3Graph field4Graph field5Graph
    tail (raw_succ M level)
    nextField1 nextField2 nextField3 nextField4 nextField5 nextFinalField
    hnextGraphs).
  exact (raw_sixFieldMasterExactProofOf_of_common_context M hPA
    nextField1 nextField2 nextField3 nextField4 nextField5 nextFinalField
    hnextProofs).
Qed.

(** The exact-ordinary-proof variant has the same represented conclusion but
    needs no second proof-packaging step. *)
Theorem raw_sixFieldMasterPackageSuccessor_of_exact_proof_components : forall
    (M : RawPAModel)
      field1Graph field2Graph field3Graph field4Graph field5Graph,
  RawSixFieldMasterExactProofComponentSuccessor M
    field1Graph field2Graph field3Graph field4Graph field5Graph ->
  RawSixFieldMasterPackageSuccessor M
    (concreteSixFieldMasterGraph
      field1Graph field2Graph field3Graph field4Graph field5Graph).
Proof.
  intros M
    field1Graph field2Graph field3Graph field4Graph field5Graph
    hsuccessor tail level hcurrent.
  destruct hcurrent as
    (currentMaster & currentCertificate & hcurrentGraph & hcurrentProof).
  destruct (hsuccessor tail level currentMaster currentCertificate
    hcurrentGraph hcurrentProof) as
    (nextField1 & nextField2 & nextField3 & nextField4 & nextField5 &
      nextFinalField & hnextGraphs & hnextProof).
  exact (raw_sixFieldMasterDirectPackage_of_components M
    field1Graph field2Graph field3Graph field4Graph field5Graph
    tail (raw_succ M level)
    nextField1 nextField2 nextField3 nextField4 nextField5 nextFinalField
    hnextGraphs hnextProof).
Qed.

End PABoundedRawCodedTruthCertificateMasterSuccessorBridge.
