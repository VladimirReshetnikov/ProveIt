import PA194PAeqUncloseHistory
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem code_lt_all (p : V) : p < ^∀ p := by
  change p < pair (6 : V) p + 1
  exact lt_of_le_of_lt (le_pair_right _ _) (lt_add_one _)
theorem code_right_lt_imp (p q : V) : q < imp PA194PAeq.language p q := by
  change q < pair (5 : V) (pair (neg PA194PAeq.language p) q) + 1
  exact lt_of_le_of_lt (le_trans (le_pair_right _ _) (le_pair_right _ _)) (lt_add_one _)
theorem inductionBody_contains_property (p : V) : p ≤ inductionBody p := by
  unfold inductionBody
  exact le_of_lt (lt_trans (code_lt_all p) (lt_trans (code_right_lt_imp _ _) (code_right_lt_imp _ _)))
theorem closedInduction_property_bound {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    p < uncloseHistory (closedInduction p) (closedInduction p) := by
  let n := formulaFreeBound (inductionBody p)
  let q := closedInduction p
  have hq : q = close n (inductionBody p) := rfl
  have hn : n ≤ q := by rw [hq]; exact close_count_le_code n (inductionBody_scope hp)
  have hentry := uncloseHistory_entry_bound q q n hn
  rw [hq,uncloseMany_close n (inductionBody p) (inductionBody_scope hp)] at hentry
  change p < uncloseHistory q q
  rw [hq]
  exact lt_of_le_of_lt (inductionBody_contains_property p) hentry
#print axioms inductionBody_contains_property
#print axioms closedInduction_property_bound
end generic
end PA194PAeqBind
