import BoundedPAConsistency.InternalRelativizationBound
import BoundedPAConsistency.ShiftBound

/-! Axiom audit for `SizedDerivation`, `InternalRelativizationBound` and `ShiftBound`. -/

open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.BoundedPAConsistency.InternalRelativizationBound
open LeanProofs.BoundedPAConsistency.ShiftBound

#print axioms pair_succ_le_exp
#print axioms tuple6_le
#print axioms DerivableLe.and
#print axioms DerivableLe.or
#print axioms relativize_le
#print axioms stage4_le
#print axioms derivableLe_relSet
#print axioms derivableLe_of_domSet
#print axioms provableLe_relativize
#print axioms provableLe_falsum_of_relativize
#print axioms shift_le_sq
#print axioms domF_le
#print axioms substs1_fvar_le
