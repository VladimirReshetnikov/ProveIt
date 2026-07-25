(**
  The remaining successor interfaces are not merely sufficient for the
  uniform theorem: they are equivalent to it.

  [CompactPAUniformProvability] reduces

    PA |- forall n, Prov_PA(code(Con_n))

  to a certificate successor available in every raw PA model.  Semantic
  soundness for [BProv] runs that reduction backwards.  Given the object-level
  derivation, every raw PA model satisfies the sealed sentence, so at every
  carrier element — standard or not — a target code and a coded proof
  certificate exist; functionality of the compact target graph identifies that
  target with any prescribed successor target.

  Two consequences are worth stating explicitly.

  First, no further *reduction* of the successor interface can make progress:
  any premise that still implies the uniform theorem is at least as strong as
  the theorem, and the certificate successor is exactly as strong.  What
  remains is a construction, not a decomposition.

  Second, the equivalence is a genuine sanity check on the whole chain.  A
  reduction target that were accidentally weaker than the goal — for instance
  one quantifying only over standard levels — could not satisfy it.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedPAProvability
  CompactPAUniformProvability.

Import ListNotations.

Module PABoundedCompactPAUniformProvabilityTightness.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedPAProvability.
Import PABoundedCompactPAUniformProvability.

(** Semantic content of the object-level derivation, at every carrier
    element of every raw PA model. *)
Theorem raw_compactSelectorPackages_of_BProv : forall
    (M : RawPAModel), RawPASatisfies M ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula ->
  forall (tail : nat -> M) (level : M),
    RawCompactSelectorPackageAt M tail level.
Proof.
  intros M hPA hprov tail level.
  pose proof (raw_sat_of_BProv_axs M
    compactUniformRestrictedPAConsistencyProvabilityFormula hPA hprov
    (fun _ : nat => raw_zero M)) as hsat.
  exact (proj1
    (raw_sat_compactUniformRestrictedPAConsistencyProvabilityFormula_iff
      M (fun _ : nat => raw_zero M)) hsat tail level).
Qed.

(** The package transformer is a consequence of the theorem it was designed
    to establish. *)
Theorem raw_restrictedPAConsistencyProofSuccessorInAllModels_of_BProv :
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula ->
  RawRestrictedPAConsistencyProofSuccessorInAllModels.
Proof.
  intros hprov M hPA level target certificate htarget hcertificate.
  destruct (raw_compactSelectorPackages_of_BProv M hPA hprov
    (fun _ : nat => raw_zero M) (raw_succ M level))
    as [nextTarget [nextCertificate [hnextTarget hnextCertificate]]].
  exists nextTarget, nextCertificate. split; assumption.
Qed.

Theorem
    raw_restrictedPAConsistencyCertificateSuccessorInAllModels_of_BProv :
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula ->
  RawRestrictedPAConsistencyCertificateSuccessorInAllModels.
Proof.
  intros hprov M hPA.
  apply (raw_restrictedPAConsistencyCertificateSuccessor_of_proof M hPA).
  exact (raw_restrictedPAConsistencyProofSuccessorInAllModels_of_BProv
    hprov M hPA).
Qed.

(** Exact characterisation of the outstanding obligation. *)
Theorem
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_iff_proofSuccessor
    : Formula.BProv Formula.Ax_s []
        compactUniformRestrictedPAConsistencyProvabilityFormula <->
  RawRestrictedPAConsistencyProofSuccessorInAllModels.
Proof.
  split.
  - exact raw_restrictedPAConsistencyProofSuccessorInAllModels_of_BProv.
  - exact PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula.
Qed.

Theorem
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_iff_certificateSuccessor
    : Formula.BProv Formula.Ax_s []
        compactUniformRestrictedPAConsistencyProvabilityFormula <->
  RawRestrictedPAConsistencyCertificateSuccessorInAllModels.
Proof.
  split.
  - exact
      raw_restrictedPAConsistencyCertificateSuccessorInAllModels_of_BProv.
  - exact
      PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_certificate_successor.
Qed.

(** Both successor interfaces are therefore interderivable *without* the
    per-model PA hypothesis being re-used: each is equivalent to the single
    object-level sentence. *)
Corollary raw_restrictedPAConsistencySuccessorInAllModels_equivalent :
  RawRestrictedPAConsistencyProofSuccessorInAllModels <->
  RawRestrictedPAConsistencyCertificateSuccessorInAllModels.
Proof.
  split; intro hstep.
  - apply
      raw_restrictedPAConsistencyCertificateSuccessorInAllModels_of_BProv.
    exact
      (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula
        hstep).
  - apply raw_restrictedPAConsistencyProofSuccessorInAllModels_of_BProv.
    exact
      (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_certificate_successor
        hstep).
Qed.

End PABoundedCompactPAUniformProvabilityTightness.
