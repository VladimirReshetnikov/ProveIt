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

theorem pair_eq_pair_iff (a b c d : R) :
    pair a b=pair c d ↔ a=c ∧ b=d := by
  constructor
  · intro he
    have hm : max a b=max c d := le_antisymm
      (le_of_not_gt (max_not_lt succ_le he.symm)) (le_of_not_gt (max_not_lt succ_le he))
    by_cases hab : a<b <;> by_cases hcd : c<d
    · have hbd : b=d := by simpa only [max_eq_right hab.le,max_eq_right hcd.le] using hm
      subst d
      have hac : a=c := add_left_cancel (by
        simpa only [pair,if_pos hab,if_pos hcd] using he)
      exact ⟨hac,rfl⟩
    · have hbc : b=c := by
        simpa only [max_eq_right hab.le,max_eq_left (le_of_not_gt hcd)] using hm
      subst c
      have hae : a=b+d := add_left_cancel (a := b*b) (by
        simpa only [pair,if_pos hab,if_neg hcd,add_assoc] using he)
      have hba : b≤a := by rw [hae]; exact le_self_add
      exact False.elim (hab.not_ge hba)
    · have had : a=d := by
        simpa only [max_eq_left (le_of_not_gt hab),max_eq_right hcd.le] using hm
      subst d
      have hce : c=a+b := add_left_cancel (a := a*a) (by
        simpa only [pair,if_neg hab,if_pos hcd,add_assoc] using he.symm)
      have hac : a≤c := by rw [hce]; exact le_self_add
      exact False.elim (hcd.not_ge hac)
    · have hac : a=c := by
        simpa only [max_eq_left (le_of_not_gt hab),max_eq_left (le_of_not_gt hcd)] using hm
      subst c
      exact ⟨rfl,add_left_cancel (by
        simpa only [pair,if_neg hab,if_neg hcd] using he)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

end ProofSimplification.ShellPairing

