(**
  The exact proof-producing successor theorem for compact selector packages.

  The closed step formula is not merely a statement that some neighboring
  packages exist.  In every raw PA model it is equivalent to the transformer
  which accepts each supplied lower target and proof certificate and returns
  a successor target and proof certificate.  By raw soundness and
  completeness, proving that one closed formula in PA is equivalent to
  implementing the all-model transformer.

  The final theorem in this file performs the remaining ordinary PA proof
  composition: the unconditional zero proof, a proof of the exact step, PA's
  induction rule, and harmless sealing of the resulting closed universal.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawModelCompleteness RawCodedPAProvability
  RawCodedFormulaOperationsStandardAdequacy RawCodedPAAxiomWitness
  CompactPAUniformProvability
  RawCodedCompactSelectorInductionSyntax
  RawCodedCompactSelectorInductionCases.

Import ListNotations.

Module PABoundedRawCodedCompactSelectorProofSuccessor.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedCompactSelectorInductionSyntax.
Import PABoundedRawCodedCompactSelectorInductionCases.

(** Raw-model soundness turns a PA proof of the step into the exact
    target/certificate transformer.  Completeness supplies the converse. *)
Theorem
    raw_restrictedPAConsistencyProofSuccessorInAllModels_iff_step_BProv :
  RawRestrictedPAConsistencyProofSuccessorInAllModels <->
  Formula.BProv Formula.Ax_s nil compactSelectorInductionStepFormula.
Proof.
  split.
  - exact PA_BProv_compactSelectorInductionStepFormula.
  - intros hstep M hPA.
    apply (proj2 (raw_compactSelectorInductionStep_exact M)).
    intro tail.
    exact (raw_sat_of_BProv_axs M
      compactSelectorInductionStepFormula hPA hstep tail).
Qed.

(** A proof of the exact closed step formula is itself an ordinary coded PA
    certificate in every raw PA model.  This is useful to proof compilers
    which consume codes rather than a meta-level [BProv] derivation. *)
Corollary raw_codedPAProofOf_compactSelectorInductionStepFormula :
    Formula.BProv Formula.Ax_s nil compactSelectorInductionStepFormula ->
  forall (M : RawPAModel), RawPASatisfies M ->
  exists certificate,
    RawCodedPAProofOf M
      (rawNumeralValue M
        (formulaCode compactSelectorInductionStepFormula))
      certificate.
Proof.
  intros hstep M hPA.
  exact (raw_codedPAProofOf_of_BProv M hPA
    compactSelectorInductionStepFormula hstep).
Qed.

(** Object-language induction from the two genuine case derivations. *)
Theorem PA_BProv_compactSelectorInductionSourceAll_of_step :
    Formula.BProv Formula.Ax_s nil compactSelectorInductionStepFormula ->
  Formula.BProv Formula.Ax_s nil
    (pAll compactSelectorInductionSourceFormula).
Proof.
  intro hstep.
  apply Formula.BProv_Ax_s_induction_rule.
  - rewrite Formula.substZero_eq_instTerm.
    rewrite <- standardFormulaSingleSubstitution_zero.
    exact PA_BProv_compactSelectorInductionZeroFormula.
  - rewrite <- standardFormulaShift_one_one_then_substitute_succ.
    exact hstep.
Qed.

(** Once the exact successor is proved, no semantic induction or additional
    compiler premise remains: this is a direct PA derivation of the requested
    sealed universal provability sentence. *)
Theorem
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_step :
    Formula.BProv Formula.Ax_s nil compactSelectorInductionStepFormula ->
  Formula.BProv Formula.Ax_s nil
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hstep.
  pose proof
    (PA_BProv_compactSelectorInductionSourceAll_of_step hstep) as hall.
  unfold compactUniformRestrictedPAConsistencyProvabilityFormula,
    Formula.sealPA.
  apply Formula.BProv_closeN_nil_of_sentences.
  - exact Formula.sentence_ax_s.
  - unfold compactUniformRestrictedPAConsistencyProvabilityBodyFormula,
      compactSelectorInductionSourceFormula in hall |- *.
    exact hall.
Qed.

(** Equivalent formulation with the original exact all-model transformer.
    The premise is retained here only to expose the proved reduction; the
    outstanding work is now precisely the left side of the equivalence
    above, not any scope, graph, base, or induction obligation. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_exact_successor
    : RawRestrictedPAConsistencyProofSuccessorInAllModels ->
  Formula.BProv Formula.Ax_s nil
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hsuccessor.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_step.
  exact (proj1
    raw_restrictedPAConsistencyProofSuccessorInAllModels_iff_step_BProv
    hsuccessor).
Qed.

End PABoundedRawCodedCompactSelectorProofSuccessor.
