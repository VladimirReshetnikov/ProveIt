import QuantifierCommutation

/-! Kernel-assumption audit for quantifier commutation and its countermodels. -/

open LeanProofs.QuantifierCommutation

#check @forall_forall_commute
#check @exists_exists_commute
#check @noExistsXY_unfold
#check @noExistsYX_unfold
#check @ExistsUnique
#check @existsUniqueXY_unfold
#check @existsUniqueYX_unfold
#check firstColumn_noExistsXY
#check firstColumn_not_noExistsYX
#check noExists_counterexample
#check noExists_swap_implication_fails
#check noExists_not_commutative
#check uniqueRelation_existsUniqueXY
#check uniqueRelation_not_existsUniqueYX
#check existsUnique_counterexample
#check existsUnique_swap_implication_fails
#check existsUnique_not_commutative

#print axioms forall_forall_commute
#print axioms exists_exists_commute
#print axioms noExistsXY_unfold
#print axioms noExistsYX_unfold
#print axioms existsUniqueXY_unfold
#print axioms existsUniqueYX_unfold
#print axioms firstColumn_noExistsXY
#print axioms firstColumn_not_noExistsYX
#print axioms noExists_counterexample
#print axioms noExists_swap_implication_fails
#print axioms noExists_not_commutative
#print axioms three_existsUnique_intro
#print axioms rowA_unique
#print axioms columnA_unique
#print axioms columnB_unique
#print axioms columnC_unique
#print axioms uniqueRelation_existsUniqueXY
#print axioms uniqueRelation_not_existsUniqueYX
#print axioms existsUnique_counterexample
#print axioms existsUnique_swap_implication_fails
#print axioms existsUnique_not_commutative
