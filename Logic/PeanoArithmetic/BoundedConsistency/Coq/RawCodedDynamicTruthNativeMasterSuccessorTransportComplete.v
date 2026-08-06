(**
  Close the context-transport seam in the native positive master successor.

  [RawCodedDynamicTruthNativeMasterSuccessorFromProofTotals] deliberately
  exposed empty-to-witnessed-context transport as a premise.  The represented
  reverse-context induction in [RawCodedPALocalProofEmptyContextTransport]
  now proves that premise in every PA model.  This file performs only the
  final, transparent specialization, so later clients cannot accidentally
  reintroduce the discharged context assumption.

  The two endpoints below remain conditional on the genuinely mathematical
  inputs: either the five positive local-proof totals, or their five native
  leaf compilers, together with the nonstandard restricted-consistency
  certificate successor.  No claim is made here that those inputs are already
  constructed.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CompactPAUniformProvability
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeCrossLevelProofCompilation
  RawCodedDynamicTruthNativeShiftProofCompilation
  RawCodedDynamicTruthNativeSubstitutionProofCompilation
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicTruthNativePositiveLocalProofTotals
  RawCodedDynamicTruthNativeMasterEndpoint
  RawCodedDynamicTruthNativeMasterSuccessorFromProofTotals
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedPALocalProofEmptyContextTransport.

Module
  PABoundedRawCodedDynamicTruthNativeMasterSuccessorTransportComplete.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativePositiveLocalProofTotals.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
Import PABoundedRawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedPALocalProofEmptyContextTransport.

(** The exact proof-total adapter with its formerly explicit transport input
    discharged by the represented context theorem. *)
Theorem
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_local_proof_totals :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativePositiveLocalProofTotals M ->
  RawRestrictedPAConsistencyCertificateSuccessor M ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA htotals hconsistencySuccessor.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_local_proof_totals_and_empty_context_transport
      M hPA htotals hconsistencySuccessor
      (raw_codedPAEmptyContextToWitnessedContextTransport M hPA)).
Qed.

(** The ordinary-proof route has the same context seam, but its six
    certificates are not restricted to the five empty-context roots.  The
    completed witnessed-context merge theorem discharges that lift directly,
    so callers now need only the genuine proof-total and compact-successor
    premises. *)
Theorem
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_proof_totals :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativePositiveProofTotals M ->
  RawRestrictedPAConsistencyCertificateSuccessor M ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA htotals hconsistencySuccessor.
  apply
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_ordinary_and_common_context_lift.
  - exact
      (raw_dynamicTruthNativeSplicedMasterPositiveOrdinaryComponentSuccessor_of_proof_totals
        M hPA htotals hconsistencySuccessor).
  - exact (raw_sixFieldMasterOrdinaryProofsCommonContextLift_complete M hPA).
Qed.

(** Direct form consumed by the five native proof-compilation layers.  Every
    propositional and quantifier shell, as well as context synchronization,
    has disappeared from the assumptions; only their leaf compilers and the
    final consistency transformer remain. *)
Corollary
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeLocalLeafRootCompiler M ->
  RawDynamicTruthNativeCrossLevelLocalRootCompiler M ->
  RawDynamicTruthNativeShiftLocalRootCompiler M ->
  RawDynamicTruthNativeSubstitutionLocalRootCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M ->
  RawRestrictedPAConsistencyCertificateSuccessor M ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA hlocal hcross hshift hsubstitution haxiomSoundness
    hconsistencySuccessor.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_local_roots_and_empty_context_transport
      M hPA hlocal hcross hshift hsubstitution haxiomSoundness
      hconsistencySuccessor
      (raw_codedPAEmptyContextToWitnessedContextTransport M hPA)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeMasterSuccessorTransportComplete.
