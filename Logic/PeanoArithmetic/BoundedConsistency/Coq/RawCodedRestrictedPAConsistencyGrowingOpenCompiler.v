(**
  A safe growing-base interface for the nonstandard certificate successor.

  The earlier dynamic-soundness base obligation asked for a local derivation
  in every caller-supplied witnessed context.  In particular it asked for
  such a derivation in the empty context, even though the raw local calculus
  has no PA-axiom rule: PA axioms enter only through a witnessed assumption
  context.  A compiler that introduces a new induction axiom must therefore
  be allowed to return the corresponding enlarged witnessed base.

  This file records exactly that interface.  It asks for an open derivation
  of bottom from the successor restricted-proof assumption in *some* honest
  witnessed PA context which is stable under the unit context shift.  The
  already verified carried closing constructors then turn that local output
  directly into the requested successor proof certificate.  No uniform
  truth or dynamic-soundness statement is asserted along the way.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedPAOpenProofComposition
  RawCodedPAProofAllNCarriedCertificates
  CompactPAUniformProvability
  RawCodedRestrictedPAConsistencyOpenCompiler.

Module PABoundedRawCodedRestrictedPAConsistencyGrowingOpenCompiler.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAOpenProofComposition.
Import PABoundedRawCodedPAProofAllNCarriedCertificates.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedRestrictedPAConsistencyOpenCompiler.

(** The output base may grow with [level].  Its witness list and context are
    existential data, but both are checked by the same represented PA-axiom
    witness relation used by ordinary proof certificates. *)
Definition RawRestrictedPAConsistencyGrowingOpenContradictionCompiler
    (M : RawPAModel) : Prop :=
  forall level target certificate successorNumeralCode : M,
    RawRestrictedPAConsistencyFormulaCodeAt M level target ->
    RawCodedPAProofOf M target certificate ->
    RawNumeralTermCodeAt M (raw_succ M level) successorNumeralCode ->
    exists grownWitnessList grownContext child : M,
      RawCodedPAAxiomWitnessContext M grownWitnessList grownContext /\
      RawContextShift M grownContext grownContext /\
      RawCodedPAOpenProofOf M grownWitnessList grownContext
        (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
        (rawFormulaBotCode M) child.

Arguments RawRestrictedPAConsistencyGrowingOpenContradictionCompiler M
  : clear implicits.

Definition
    RawRestrictedPAConsistencyGrowingOpenContradictionCompilerInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedPAConsistencyGrowingOpenContradictionCompiler M.

(** The successor target's transparent graph supplies its exact numeral-code
    view.  The growing compiler supplies an honest carried open proof, and
    the existing closing theorem packages implication introduction,
    universal introduction, and the fixed outer seal. *)
Theorem
    raw_restrictedPAConsistencyCertificateSuccessor_of_growingOpenCompiler :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawRestrictedPAConsistencyGrowingOpenContradictionCompiler M ->
  RawRestrictedPAConsistencyCertificateSuccessor M.
Proof.
  intros M hPA hcompiler level target certificate nextTarget
    htarget hcertificate hnextTarget.
  destruct (raw_restrictedPAConsistencyFormulaCodeAt_open_view
    M (raw_succ M level) nextTarget hnextTarget)
    as [successorNumeralCode [hnumeral hnextTargetView]].
  destruct (hcompiler level target certificate successorNumeralCode
    htarget hcertificate hnumeral) as
    (grownWitnessList & grownContext & child &
      hwitness & hselfShift & hopen).
  exists (rawProofSealedUniversalOpenNegationCarriedCertificate M
    grownWitnessList grownContext
    (restrictedTargetFormulaContextBound
      restrictedPAConsistencyBodyFormulaContext)
    (rawRestrictedPAProofAssumptionCode M successorNumeralCode) child).
  rewrite hnextTargetView.
  exact
    (raw_codedPAProofOf_sealed_universal_negation_of_carried_open_bottom
      M hPA grownWitnessList grownContext
      (restrictedTargetFormulaContextBound
        restrictedPAConsistencyBodyFormulaContext)
      (rawRestrictedPAProofAssumptionCode M successorNumeralCode)
      child hselfShift hopen).
Qed.

Corollary
    raw_restrictedPAConsistencyCertificateSuccessorInAllModels_of_growingOpenCompiler
    : RawRestrictedPAConsistencyGrowingOpenContradictionCompilerInAllModels ->
  RawRestrictedPAConsistencyCertificateSuccessorInAllModels.
Proof.
  intros hcompiler M hPA.
  exact
    (raw_restrictedPAConsistencyCertificateSuccessor_of_growingOpenCompiler
      M hPA (hcompiler M hPA)).
Qed.

(** This is the corrected conditional endpoint for a future staged truth
    compiler.  Its sole premise is proof-producing and may enlarge the
    witnessed PA base; it does not require an impossible exact-context base
    proof and does not require generic proof-tree weakening. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_growingOpenCompiler
    : RawRestrictedPAConsistencyGrowingOpenContradictionCompilerInAllModels ->
  Formula.BProv Formula.Ax_s nil
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hcompiler.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_certificate_successor.
  exact
    (raw_restrictedPAConsistencyCertificateSuccessorInAllModels_of_growingOpenCompiler
      hcompiler).
Qed.

End PABoundedRawCodedRestrictedPAConsistencyGrowingOpenCompiler.
