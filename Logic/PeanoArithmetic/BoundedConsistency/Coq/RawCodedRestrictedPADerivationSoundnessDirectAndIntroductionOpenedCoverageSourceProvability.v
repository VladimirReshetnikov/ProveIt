(** PA provability of the fixed opened And-I coverage source. *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceDefinitions
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceSemanticValidity.

Import ListNotations.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceProvability.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceDefinitions.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceSemanticValidity.

Theorem PA_proves_coqRestrictedPADirectAndIntroductionOpenedCoverageSource :
  Formula.BProv Formula.Ax_s []
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        coqRestrictedPADirectAndIntroductionOpenedCoverageSourceFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact
        (raw_coqRestrictedPADirectAndIntroductionOpenedCoverageSource_valid
          M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceProvability.
