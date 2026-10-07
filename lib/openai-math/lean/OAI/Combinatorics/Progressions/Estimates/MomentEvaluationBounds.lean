import OAI.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
import OAI.Combinatorics.Progressions.Polynomial.FiniteMomentPolynomial

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def momentWeightBound (m : ℕ) : ℕ := (m + 1) * (m * m + 1) ^ m

theorem momentWeightBound_pos (m : ℕ) : 0 < momentWeightBound m := by
  unfold momentWeightBound
  positivity

theorem norm_momentWeight_le {m : ℕ} (z : Fin (m * m + 1)) (j : Fin m) :
    ‖(z.val : ℂ) ^ j.val‖ ≤ ((m * m + 1) ^ m : ℕ) := by
  rw [norm_pow, Complex.norm_natCast]
  have hz : (z.val : ℝ) ≤ (m * m + 1 : ℕ) := by exact_mod_cast (Nat.le_of_lt z.isLt)
  calc
    _ ≤ ((m * m + 1 : ℕ) : ℝ) ^ j.val := pow_le_pow_left₀ (Nat.cast_nonneg _) hz _
    _ ≤ ((m * m + 1 : ℕ) : ℝ) ^ m :=
      pow_le_pow_right₀ (by exact_mod_cast (Nat.le_add_left 1 (m * m))) (Nat.le_of_lt j.isLt)
    _ = _ := by norm_cast

noncomputable def momentLinear {m : ℕ} (v : Fin m → ℂ) (z : Fin (m * m + 1)) : ℂ :=
  ∑ j, v j * (z.val : ℂ) ^ j.val

theorem norm_momentLinear_le {m : ℕ} (v : Fin m → ℂ) (z : Fin (m * m + 1))
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ j, ‖v j‖ ≤ M) :
    ‖momentLinear v z‖ ≤ (momentWeightBound m : ℝ) * M := by
  calc
    _ ≤ ∑ j, ‖v j‖ * ‖(z.val : ℂ) ^ j.val‖ := by
      simpa only [momentLinear, norm_mul] using norm_sum_le (s := Finset.univ)
        (f := fun j => v j * (z.val : ℂ) ^ j.val)
    _ ≤ ∑ _j : Fin m, M * (((m * m + 1) ^ m : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul (hv j) (norm_momentWeight_le z j) (norm_nonneg _) hM)
    _ ≤ (momentWeightBound m : ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, momentWeightBound]
      push_cast
      nlinarith [mul_nonneg hM (pow_nonneg (by positivity : (0 : ℝ) ≤ m * m + 1) m)]

theorem momentLinear_lipschitz {m : ℕ} {X : Type*} [PseudoMetricSpace X]
    (f : Fin m → X → ℂ) {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j))
    (z : Fin (m * m + 1)) :
    LipschitzWith ((momentWeightBound m : ℝ≥0) * K) (fun x => momentLinear (fun j => f j x) z) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have heq : momentLinear (fun j => f j x) z - momentLinear (fun j => f j y) z =
      momentLinear (fun j => f j x - f j y) z := by
    simp only [momentLinear, Finset.sum_sub_distrib, sub_mul]
  rw [heq]
  calc
    _ ≤ (momentWeightBound m : ℝ) * ((K : ℝ) * dist x y) :=
      norm_momentLinear_le _ z (by positivity)
        (fun j => by simpa only [dist_eq_norm] using (hf j).dist_le_mul x y)
    _ = _ := by push_cast; ring

end Erdos3

end

end OAI
