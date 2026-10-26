import Std

/-! Exact replacements for the two elementary `wholeShift` lemmas. -/
namespace DiophantineConsistencyProofReview.BasicNat

def wholeShift (t : Nat) : Nat := t - t % 2011

theorem wholeShift_dvd (t : Nat) : 2011 ∣ wholeShift t :=
  ⟨t / 2011, Nat.mul_div_self_eq_mod_sub_self.symm⟩

theorem wholeShift_add_remainder (t : Nat) : wholeShift t + t % 2011 = t :=
  Nat.sub_add_cancel (Nat.mod_le t 2011)

#print axioms wholeShift_dvd
#print axioms wholeShift_add_remainder

end DiophantineConsistencyProofReview.BasicNat
