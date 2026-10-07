import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

def primitiveCorrectionRadius (s u b i : ℕ) (L M : ℝ) : ℝ :=
  (((u + b : ℕ) : ℝ) + 1) ^ s * M * (max 1 ((i : ℝ) * L)) ^ s

theorem primitiveCorrectionRadius_nonneg (s u b i : ℕ) (L : ℝ) {M : ℝ}
    (hM : 0 ≤ M) : 0 ≤ primitiveCorrectionRadius s u b i L M := by
  unfold primitiveCorrectionRadius
  positivity

theorem primitiveCorrectionRadius_le_exp (s u b i : ℕ) {p t L M : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hu : (u : ℝ) ≤ p) (hb : (b : ℝ) ≤ p) (hi : (i : ℝ) ≤ p)
    (hM : 0 ≤ M) (hMcap : M ≤ Real.exp t) (hLcap : L ≤ Real.exp t) :
    primitiveCorrectionRadius s u b i L M ≤
      Real.exp ((s : ℝ) * (3 * p + 1) + (s + 1) * t) := by
  have hbase : ((u + b : ℕ) : ℝ) + 1 ≤ Real.exp (2 * p + 1) := by
    rw [Nat.cast_add]
    linarith [Real.add_one_le_exp (2 * p + 1)]
  have hie : (i : ℝ) ≤ Real.exp p :=
    hi.trans (by linarith [Real.add_one_le_exp p])
  have hmax : max 1 ((i : ℝ) * L) ≤ Real.exp (p + t) := by
    apply max_le
    · exact Real.one_le_exp (add_nonneg hp ht)
    · calc
        _ ≤ (i : ℝ) * Real.exp t := mul_le_mul_of_nonneg_left hLcap (Nat.cast_nonneg _)
        _ ≤ Real.exp p * Real.exp t :=
          mul_le_mul_of_nonneg_right hie (Real.exp_nonneg _)
        _ = Real.exp (p + t) := (Real.exp_add _ _).symm
  calc
    primitiveCorrectionRadius s u b i L M ≤
        (Real.exp (2 * p + 1)) ^ s * Real.exp t * (Real.exp (p + t)) ^ s := by
      unfold primitiveCorrectionRadius
      apply mul_le_mul
      · exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase s) hMcap hM
          (by positivity)
      · exact pow_le_pow_left₀ (by positivity) hmax s
      · positivity
      · positivity
    _ = Real.exp ((s : ℝ) * (3 * p + 1) + (s + 1) * t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem primitive_correction_radius_bound (s u b i : ℕ) {p t L M : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t)
    (hu : (u : ℝ) ≤ p) (hb : (b : ℝ) ≤ p) (hi : (i : ℝ) ≤ p)
    (hM : 0 ≤ M) (hMcap : M ≤ Real.exp t) (hLcap : L ≤ Real.exp t) :
    let Rcap := (((u + b : ℕ) : ℝ) + 1) ^ s * M * (max 1 ((i : ℝ) * L)) ^ s
    0 ≤ Rcap ∧ Rcap ≤ Real.exp ((s : ℝ) * (3 * p + 1) + (s + 1) * t) :=
  ⟨primitiveCorrectionRadius_nonneg s u b i L hM,
    primitiveCorrectionRadius_le_exp s u b i hp ht hu hb hi hM hMcap hLcap⟩

end Erdos3

end

end OAI
