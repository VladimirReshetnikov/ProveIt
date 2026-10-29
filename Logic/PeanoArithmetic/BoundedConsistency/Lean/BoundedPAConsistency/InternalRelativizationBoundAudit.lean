import BoundedPAConsistency.InternalRelativizationBound

/-! Axiom audit for `SizedDerivation` and `InternalRelativizationBound`. -/

open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.BoundedPAConsistency.InternalRelativizationBound

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
