import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Tactic.Ring

noncomputable section
namespace ProofSimplification.ShellPairing
variable {R : Type*} [CommSemiring R] [LinearOrder R] [CanonicallyOrderedAdd R]
  [IsStrictOrderedRing R]

def pair (a b : R) : R := if a<b then b*b+a else a*a+a+b

private theorem square_le_square {a b : R} (h : a≤b) : a*a≤b*b :=
  mul_le_mul h h (zero_le : 0≤a) (zero_le : 0≤b)

omit [IsStrictOrderedRing R] in
theorem max_square_le_pair (a b : R) :
    (max a b)*(max a b)≤pair a b := by
  by_cases h : a<b
  · simp only [pair,if_pos h,max_eq_right h.le]
    exact le_self_add
  · simp only [pair,if_neg h,max_eq_left (le_of_not_gt h)]
    exact le_self_add.trans le_self_add

theorem pair_lt_next_square (a b : R) :
    pair a b<(max a b+1)*(max a b+1) := by
  by_cases h : a<b
  · simp only [pair,if_pos h,max_eq_right h.le]
    have hb : b≤b+b := le_self_add
    have hb' : b+b≤b+b+1 := le_self_add
    have ha : a<b+b+1 := h.trans_le (hb.trans hb')
    calc
      b*b+a < b*b+(b+b+1) := by
        simpa only [add_comm] using add_lt_add_left ha (b*b)
      _ = (b+1)*(b+1) := by ring
  · simp only [pair,if_neg h,max_eq_left (le_of_not_gt h)]
    calc
      a*a+a+b ≤ a*a+a+a := by
        simpa only [add_comm] using add_le_add_left (le_of_not_gt h) (a*a+a)
      _ < a*a+a+a+1 := lt_add_of_pos_right _ zero_lt_one
      _ = (a+1)*(a+1) := by ring

variable (succ_le : ∀ a b : R,a<b → a+1≤b)
include succ_le

private theorem max_not_lt {a b c d : R}
    (he : pair a b=pair c d) :
    ¬ max a b<max c d := by
  intro h
  have hnext : max a b+1≤max c d := succ_le _ _ h
  have hup := (pair_lt_next_square a b).trans_le
    ((square_le_square hnext).trans (max_square_le_pair c d))
  exact hup.ne he

/- The shell midpoint recovers which branch produced the output. -/
omit succ_le in
theorem pair_lt_shell_cut (a b : R) :
    pair a b < (max a b)*(max a b)+max a b ↔ a<b := by
  by_cases hab : a<b
  · simp only [pair,if_pos hab,max_eq_right hab.le,add_lt_add_iff_left]
  · simp only [pair,if_neg hab,max_eq_left (le_of_not_gt hab)]
    exact iff_of_false (not_lt_of_ge le_self_add) hab

theorem pair_eq_pair_iff (a b c d : R) :
    pair a b=pair c d ↔ a=c ∧ b=d := by
  constructor
  · intro he
    have hm : max a b=max c d := le_antisymm
      (le_of_not_gt (max_not_lt succ_le he.symm)) (le_of_not_gt (max_not_lt succ_le he))
    have hbranch : a<b ↔ c<d := by
      rw [← pair_lt_shell_cut a b,← pair_lt_shell_cut c d,he,hm]
    by_cases hab : a<b
    · have hcd := hbranch.mp hab
      have hbd : b=d := by simpa only [max_eq_right hab.le,max_eq_right hcd.le] using hm
      subst d
      exact ⟨add_left_cancel (by simpa only [pair,if_pos hab,if_pos hcd] using he),rfl⟩
    · have hcd : ¬c<d := fun h => hab (hbranch.mpr h)
      have hac : a=c := by
        simpa only [max_eq_left (le_of_not_gt hab),max_eq_left (le_of_not_gt hcd)] using hm
      subst c
      exact ⟨rfl,add_left_cancel (by simpa only [pair,if_neg hab,if_neg hcd] using he)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

#print axioms pair_lt_shell_cut
#print axioms pair_eq_pair_iff

end ProofSimplification.ShellPairing

