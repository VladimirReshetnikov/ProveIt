(**
  PA provability of the complete opened Or-I-left coverage law.

  The expensive semantic argument lives in the neighboring validity module.
  Keeping this completeness wrapper separate means Rocq can cache that
  arbitrary-model proof while checking the closed PA derivation below.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageSource
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageProvability.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawModelCompleteness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageSource.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.

(** Arithmetic completeness first proves the sealed sentence.  Universal
    elimination then reopens the original formula without changing its free
    variables (there are none beyond the displayed outer level binder). *)
Theorem
    PA_proves_coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource :
  Formula.BProv Formula.Ax_s []
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact
        (raw_coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource_valid
          M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageProvability.
