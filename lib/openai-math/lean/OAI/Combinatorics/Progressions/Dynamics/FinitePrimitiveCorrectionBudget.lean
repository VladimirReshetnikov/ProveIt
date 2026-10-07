import OAI.Combinatorics.Progressions.Dynamics.PrimitiveCorrectionRadiusBudget
import OAI.Combinatorics.Progressions.Sampling.BoundedKernelGridEnumerationBudget

namespace OAI

section

namespace Erdos3

private theorem primitive_correction_denominator_bound (q d s : ℕ) {t : ℝ}
    (hq : (q : ℝ) ≤ Real.exp t) (hd : (d : ℝ) ≤ Real.exp t) :
    ((q * d ^ s : ℕ) : ℝ) ≤ Real.exp (((s : ℝ) + 1) * t) := by
  have hp : ((d ^ s : ℕ) : ℝ) ≤ Real.exp ((s : ℝ) * t) := by
    rw [Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg d) hd s).trans_eq (Real.exp_nat_mul t s).symm
  calc
    _ = (q : ℝ) * ((d ^ s : ℕ) : ℝ) := by rw [Nat.cast_mul]
    _ ≤ Real.exp t * Real.exp ((s : ℝ) * t) :=
      mul_le_mul hq hp (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (((s : ℝ) + 1) * t) := by rw [← Real.exp_add]; congr 1; ring

private theorem primitive_correction_dimension_bound (u i r s : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hu : (u : ℝ) ≤ p) (hi : (i : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) :
    ((((u + i + 1) ^ s) * r : ℕ) : ℝ) ≤ p * (2 * p + 1) ^ s := by
  have hbase : ((u + i + 1 : ℕ) : ℝ) ≤ 2 * p + 1 := by push_cast; linarith
  have hpw := pow_le_pow_left₀ (Nat.cast_nonneg (u + i + 1)) hbase s
  push_cast at hpw
  push_cast
  calc
    _ ≤ (2 * p + 1) ^ s * p :=
      mul_le_mul hpw hr (Nat.cast_nonneg _) (pow_nonneg (by positivity) s)
    _ = _ := mul_comm _ _

theorem exists_finite_primitive_correction_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (u b i r q d : ℕ) (p L M : ℝ),
      0 ≤ p → (u : ℝ) ≤ p → (b : ℝ) ≤ p → (i : ℝ) ≤ p → (r : ℝ) ≤ p →
      (q : ℝ) ≤ Real.exp ((p + a) ^ a) → (d : ℝ) ≤ Real.exp ((p + a) ^ a) →
      L ≤ Real.exp ((p + a) ^ a) → 0 ≤ M → M ≤ Real.exp ((p + a) ^ a) →
      let Rcap := ((((u + b : ℕ) : ℝ) + 1) ^ s * M) * (max 1 ((i : ℝ) * L)) ^ s
      ((((2 * ⌈((q * d ^ s : ℕ) : ℝ) * Rcap⌉₊ + 3) ^ ((u + i + 1) ^ s)) ^ r : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := X * (2 * X + 1) ^ s + Polynomial.C s * (3 * X + 1) +
    Polynomial.C (s + 1) * (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro u b i r q d p L M hp hu hb hi hr hq hd hL hM hMcap Rcap
  let t := (p + a) ^ a
  have ht : 0 ≤ t := by dsimp [t]; positivity
  let p' := p * (2 * p + 1) ^ s + (s : ℝ) * (3 * p + 1) + ((s : ℝ) + 1) * t
  have hp' : 0 ≤ p' := by dsimp [p']; positivity
  have hfirst0 : 0 ≤ p * (2 * p + 1) ^ s := by positivity
  have hmid0 : 0 ≤ (s : ℝ) * (3 * p + 1) := by positivity
  have hlast0 : 0 ≤ ((s : ℝ) + 1) * t := by positivity
  have hdim : ((((u + i + 1) ^ s) * r : ℕ) : ℝ) ≤ p' :=
    (primitive_correction_dimension_bound u i r s hp hu hi hr).trans (by dsimp [p']; linarith)
  have hdenom : ((q * d ^ s : ℕ) : ℝ) ≤ Real.exp p' :=
    (primitive_correction_denominator_bound q d s hq hd).trans
      (Real.exp_le_exp.mpr (by dsimp [p']; linarith))
  have hR := primitiveCorrectionRadius_le_exp s u b i hp ht hu hb hi hM hMcap hL
  have hR0 : 0 ≤ Rcap := primitiveCorrectionRadius_nonneg s u b i L hM
  have hRcap : Rcap ≤ Real.exp p' := hR.trans
    (Real.exp_le_exp.mpr (by dsimp [p']; linarith))
  have hcount := real_grid_window_count_le_exp (((u + i + 1) ^ s) * r) (q * d ^ s)
    hp' hR0 hdim hdenom hRcap
  rw [pow_mul] at hcount
  exact hcount.trans (Real.exp_le_exp.mpr (by
    simpa [P, X, p', t, Polynomial.eval₂_pow] using hbudget p hp))

end Erdos3

end

end OAI
