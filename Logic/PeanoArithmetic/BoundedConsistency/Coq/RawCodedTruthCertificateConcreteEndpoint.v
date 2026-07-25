(**
  Concrete six-field endpoint for uniform internal PA provability.

  The preceding modules deliberately expose the base and successor
  constructions separately.  This file joins those construction-level
  interfaces to the generic master induction, so the remaining obligation is
  stated once and cannot drift away from the exact object-language target.

  Five fixed output-first graphs are supplied in Lean's dependency order:

    local, cross-level, shift, substitution, axiom-soundness.

  In every raw PA model, the caller must provide the checked zero package and
  one of the two checked component successor compilers.  The assembler itself
  supplies graph decomposition.  Consequently the theorem below concludes
  the literal compact sentence

    PA |- forall n, exists p, Code(Con_n, n) /\ Prov_PA(p).

  This module is a connector, not an unconditional endpoint: the concrete
  dynamic-field base and successor packages still have to be constructed.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CompactPAUniformProvability
  RawCodedTruthCertificateMasterInduction
  RawCodedTruthCertificateMasterAssembler
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterSuccessorBridge.

Module PABoundedRawCodedTruthCertificateConcreteEndpoint.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedTruthCertificateMasterInduction.
Import PABoundedRawCodedTruthCertificateMasterAssembler.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterSuccessorBridge.

(** Either successor interface is sufficient.  The left branch returns six
    local proofs in one witnessed PA context; the right branch has already
    packaged those proofs into an exact ordinary certificate. *)
Definition RawSixFieldMasterComponentSuccessor (M : RawPAModel)
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    : Prop :=
  RawSixFieldMasterRawComponentSuccessor M
    field1Graph field2Graph field3Graph field4Graph field5Graph \/
  RawSixFieldMasterExactProofComponentSuccessor M
    field1Graph field2Graph field3Graph field4Graph field5Graph.

Arguments RawSixFieldMasterComponentSuccessor
  M field1Graph field2Graph field3Graph field4Graph field5Graph
    : clear implicits.

(** The exact concrete data still missing from the Coq port.  Quantifying
    over all raw PA models is essential: [level] may be nonstandard. *)
Definition RawConcreteSixFieldMasterComponentsInAllModels
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawSixFieldMasterZeroComponentPackage M
      field1Graph field2Graph field3Graph field4Graph field5Graph /\
    RawSixFieldMasterComponentSuccessor M
      field1Graph field2Graph field3Graph field4Graph field5Graph.

Arguments RawConcreteSixFieldMasterComponentsInAllModels
  field1Graph field2Graph field3Graph field4Graph field5Graph
    : clear implicits.

(** Assemble the three callbacks consumed by PA-definable master induction.
    Decomposition is unconditional for the transparent six-field graph; the
    two remaining callbacks are exactly the supplied component packages. *)
Theorem raw_sixFieldMasterInductionCallbacks_of_components : forall
    field1Graph field2Graph field3Graph field4Graph field5Graph,
  RawConcreteSixFieldMasterComponentsInAllModels
    field1Graph field2Graph field3Graph field4Graph field5Graph ->
  RawSixFieldMasterInductionCallbacksInAllModels
    (concreteSixFieldMasterGraph
      field1Graph field2Graph field3Graph field4Graph field5Graph).
Proof.
  intros field1Graph field2Graph field3Graph field4Graph field5Graph
    hcomponents M hPA.
  destruct (hcomponents M hPA) as [hbase hsuccessor].
  split.
  - exact (concreteSixFieldMasterGraph_decomposition M
      field1Graph field2Graph field3Graph field4Graph field5Graph).
  - split.
    + exact (raw_sixFieldMasterPackageBase_of_components M hPA
        field1Graph field2Graph field3Graph field4Graph field5Graph hbase).
    + destruct hsuccessor as [hraw | hexact].
      * exact (raw_sixFieldMasterPackageSuccessor_of_raw_components M hPA
          field1Graph field2Graph field3Graph field4Graph field5Graph hraw).
      * exact
          (raw_sixFieldMasterPackageSuccessor_of_exact_proof_components M
            field1Graph field2Graph field3Graph field4Graph field5Graph
            hexact).
Qed.

(** Fully connected conditional endpoint for the requested object theorem.
    Once the concrete five-field component package above is constructed, no
    further semantic or syntactic bridge remains. *)
Theorem
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_components
    : forall field1Graph field2Graph field3Graph field4Graph field5Graph,
  RawConcreteSixFieldMasterComponentsInAllModels
    field1Graph field2Graph field3Graph field4Graph field5Graph ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intros field1Graph field2Graph field3Graph field4Graph field5Graph
    hcomponents.
  apply
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_sixFieldMaster
      (concreteSixFieldMasterGraph
        field1Graph field2Graph field3Graph field4Graph field5Graph)).
  exact (raw_sixFieldMasterInductionCallbacks_of_components
    field1Graph field2Graph field3Graph field4Graph field5Graph hcomponents).
Qed.

End PABoundedRawCodedTruthCertificateConcreteEndpoint.
