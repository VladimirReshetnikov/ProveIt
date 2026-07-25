import BoundedZFCConsistency.LevelCollapse

/-!
# Kernel audit for the level-collapse theorem

This deliberately small module checks the public interface of
`BoundedZFCConsistency.LevelCollapse` and prints the axioms of its substantive
theorems.  Keeping the audit separate prevents diagnostic output from becoming
part of the library-facing module.

The last section is the point of the audit: `levelTwoValuedAt` discharges
`BoundedZFCConsistency.LevelSoundness.LevelTwoValuedAt` outright, so it must be
seen to rest on nothing beyond the ambient classical axioms.
-/

namespace LeanProofs.BoundedZFCConsistency.LevelCollapseAudit

open SetTheory
open LeanProofs.BoundedZFCConsistency

/-! ## Weakening and descent for the oriented bounds -/

#check @sigmaBounded_le
#check @piBounded_le
#check @sigmaBounded_natV_le
#check @piBounded_natV_le
#check @sigmaBounded_or_piBounded
#check @sigmaBounded_imp
#check @piBounded_imp
#check @sigmaBounded_and
#check @piBounded_and
#check @sigmaBounded_or
#check @piBounded_or
#check @piBounded_all
#check @sigmaBounded_ex
#check @piBounded_of_sigmaBounded_all
#check @sigmaBounded_of_piBounded_ex
#check @piBounded_of_sigmaBounded_all_succ
#check @sigmaBounded_of_piBounded_ex_succ
#check @piBounded_of_sigmaBounded_all_eq_succ
#check @sigmaBounded_of_piBounded_ex_eq_succ
#check @not_sigmaBounded_zero_all
#check @not_piBounded_zero_ex

#print axioms sigmaBounded_imp
#print axioms piBounded_imp
#print axioms piBounded_of_sigmaBounded_all
#print axioms sigmaBounded_of_piBounded_ex
#print axioms piBounded_of_sigmaBounded_all_succ
#print axioms sigmaBounded_of_piBounded_ex_succ

/-! ## The introduction halves at level zero -/

#check @sigmaTrue_zero_imp_intro
#check @piFalse_zero_imp_intro
#check @sigmaTrue_zero_and_intro
#check @piFalse_zero_and_intro
#check @sigmaTrue_zero_or_intro
#check @piFalse_zero_or_intro

/-! ## The collapse property, its definability, and the two inductions -/

#check @CollapseAt
#check @collapseF
#check @envCollapse
#check @collapseF_spec
#check @levelSat_collapse_tag_low
#check @collapse_zero
#check @collapse_succ
#check @collapseAt_of_isFormCodeSem

#print axioms collapse_zero
#print axioms collapse_succ

/-! ## The level-collapse theorem and its iterations -/

#check @sigmaTrue_collapse
#check @piFalse_collapse
#check @sigmaTrue_collapse_le
#check @piFalse_collapse_le
#check @sigmaTrue_collapse_iff
#check @piFalse_collapse_iff
#check @piTrue_mono

#print axioms sigmaTrue_collapse
#print axioms piFalse_collapse
#print axioms sigmaTrue_collapse_le
#print axioms piFalse_collapse_le
#print axioms piTrue_mono

/-! ## Locating the delegation level, and exclusivity -/

#check @sigmaTrue_all_inv'
#check @piFalse_ex_inv'
#check @ExclAt
#check @exclF
#check @envExcl
#check @exclF_spec
#check @sigmaTrue_not_piFalse
#check @piTrue_of_sigmaTrue

#print axioms sigmaTrue_all_inv'
#print axioms piFalse_ex_inv'
#print axioms sigmaTrue_not_piFalse

/-! ## Totality -/

#check @exists_pred_piBounded_of_sigmaBounded_all
#check @exists_pred_sigmaBounded_of_piBounded_ex
#check @piFalse_memAtom_of_not
#check @piFalse_eqAtom_of_ne
#check @imp_total_step
#check @and_total_step
#check @or_total_step
#check @TotalAt
#check @totalF
#check @totalF_spec
#check @totalAt_of_isFormCodeSem

#print axioms totalAt_of_isFormCodeSem

/-! ## The polarity switches as biconditionals -/

#check @sigmaTrue_all_elim
#check @sigmaTrue_all
#check @piFalse_ex_elim
#check @piFalse_ex

#print axioms sigmaTrue_all
#print axioms piFalse_ex

/-! ## Two-valuedness, and the obligation it discharges

`levelTwoValuedAt` closes `LevelTwoValuedAt`, the second of the three
obligations named in `BoundedZFCConsistency.LevelSoundness`.  Of the remaining
two, `LevelSoundnessAt` was blocked on precisely this one, and
`AxiomCodesTrueAt` is independent of both. -/

#check @sigmaTrue_or_piFalse
#check @sigmaTrue_iff_piTrue
#check @levelTwoValuedAt

#print axioms sigmaTrue_or_piFalse
#print axioms sigmaTrue_iff_piTrue
#print axioms levelTwoValuedAt

end LeanProofs.BoundedZFCConsistency.LevelCollapseAudit
