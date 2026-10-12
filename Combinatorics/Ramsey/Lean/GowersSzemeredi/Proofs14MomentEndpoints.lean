import GowersSzemeredi.Proofs14HigherArrangements

/-! The higher-moment implication also includes zero and negative lower-bound
parameters: these give a nonpositive conclusion against a nonnegative count. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def lemma_14_7_all_real_parameters : Prop :=
  ∀ (N k : Nat) [NeZero N] (theta : Real)
      (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N),
    theta * (N : Real) ^ (5 * k + 3) ≤
        respectedGeneralArrangementCount 2 B phi →
    theta ^ 7 * (N : Real) ^ (17 * k + 15) ≤
      respectedGeneralArrangementCount 8 B phi

/-- Recover the unrestricted real theta range of Lemma14.7. -/
theorem lemma_14_7_all_real_parameters_holds : lemma_14_7_all_real_parameters := by
  intro N k _ theta B phi hcount
  by_cases ht : 0 < theta
  · exact lemma_14_7_holds N k theta B phi ht hcount
  · have ht0 : theta ≤ 0 := le_of_not_gt ht
    have h6 : 0 ≤ theta ^ (6 : Nat) := by
      have hs := sq_nonneg (theta ^ (3 : Nat))
      simpa only [← pow_mul] using hs
    have h7 : theta ^ (7 : Nat) ≤ 0 := by
      calc
        _ = theta * theta ^ (6 : Nat) := by ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht0 h6
    exact (mul_nonpos_of_nonpos_of_nonneg h7 (by positivity)).trans (Nat.cast_nonneg _)

end LeanProofs.GowersSzemeredi
