(**
  Public compact endpoint after context transport.

  The native master endpoint consumes a six-field successor whose six proof
  roots already share one witnessed PA context.  The transport-complete
  successor module proves that synchronization from ordinary proof totals:
  it reconstructs each hidden witness context and transports the five native
  roots into the context carried by the compact-consistency certificate.

  This file only performs the final all-model specialization.  It does not
  add a semantic truth-to-proof principle and it does not hide any of the
  five native proof-producing totals or the compact-consistency successor.
  Thus the resulting theorem is a sharper public boundary than the generic
  callback endpoint, while remaining honest about the still-open leaf
  compilers.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFRawSemantics.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CompactPAUniformProvability
  RawModelCompleteness
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeCrossLevelProofCompilation
  RawCodedDynamicTruthNativeShiftProofCompilation
  RawCodedDynamicTruthNativeSubstitutionProofCompilation
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicTruthNativeMasterSuccessorFromProofTotals
  RawCodedDynamicTruthNativeMasterEndpoint
  RawCodedDynamicTruthNativeMasterSuccessorTransportComplete.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeMasterEndpointWithTransport.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PABoundedRawModelCompleteness.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
Import PABoundedRawCodedDynamicTruthNativeMasterSuccessorTransportComplete.

(** The five ordinary positive proof totals, uniformly over all PA models. *)
Definition RawDynamicTruthNativePositiveProofTotalsInAllModels : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawDynamicTruthNativePositiveProofTotals M.

Arguments RawDynamicTruthNativePositiveProofTotalsInAllModels : clear implicits.

(** The direct five-root interface is the corresponding leaf-compiler form. *)
Definition RawDynamicTruthNativeLocalRootCompilersInAllModels : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawDynamicTruthNativeLocalLeafRootCompiler M /\
    RawDynamicTruthNativeCrossLevelLocalRootCompiler M /\
    RawDynamicTruthNativeShiftLocalRootCompiler M /\
    RawDynamicTruthNativeSubstitutionLocalRootCompiler M /\
    RawDynamicTruthNativeAxiomSoundnessLocalRootCompiler M.

Arguments RawDynamicTruthNativeLocalRootCompilersInAllModels
  : clear implicits.

(** Context transport now discharges the public successor package directly. *)
Theorem
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels_of_proof_totals
    : RawDynamicTruthNativePositiveProofTotalsInAllModels ->
  RawRestrictedPAConsistencyCertificateSuccessorInAllModels ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels.
Proof.
  intros htotals hconsistency M hPA.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_proof_totals
      M hPA (htotals M hPA) (hconsistency M hPA)).
Qed.

(** The same endpoint with all five leaf compilers exposed explicitly. *)
Theorem
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels_of_local_root_compilers
    : RawDynamicTruthNativeLocalRootCompilersInAllModels ->
  RawRestrictedPAConsistencyCertificateSuccessorInAllModels ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels.
Proof.
  intros hroots hconsistency M hPA.
  destruct (hroots M hPA) as
    [hlocal [hcross [hshift [hsubstitution haxiomSoundness]]]].
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_local_roots
      M hPA hlocal hcross hshift hsubstitution haxiomSoundness
      (hconsistency M hPA)).
Qed.

(** Final compact uniform-provability theorem from ordinary proof totals. *)
Theorem
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_proof_totals
    : RawDynamicTruthNativePositiveProofTotalsInAllModels ->
  RawRestrictedPAConsistencyCertificateSuccessorInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intros htotals hconsistency.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_native_compiler.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels_of_proof_totals
      htotals hconsistency).
Qed.

(** Final compact uniform-provability theorem from the five native leaf
    compilers.  This is the most direct remaining boundary in this branch. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_local_root_compilers
    : RawDynamicTruthNativeLocalRootCompilersInAllModels ->
  RawRestrictedPAConsistencyCertificateSuccessorInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intros hroots hconsistency.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_native_compiler.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels_of_local_root_compilers
      hroots hconsistency).
Qed.

End PABoundedRawCodedDynamicTruthNativeMasterEndpointWithTransport.
