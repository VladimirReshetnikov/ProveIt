import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Exact positive-power homogeneity of the common-multiplier height

A standalone, kernel-checkable generalization of `New.HeightLe` from
`New/Reduction/Lattices/Heights.lean` at ProveIt commit
`9050b04000647d588d0c78d945180abcd3b0bcf7`.

The only abstraction is that the local normed fields and their maps from `ℂ`
are parameters. The original definition specializes these parameters to
`ι = New.PrimePadicIso`, `prime ι = ι.prime`, `F ι = PadicAlgCl ι.prime`, and
`localMap ι = ι.iso.toRingHom`. The multiplier, all complex automorphisms,
nonnegative finite-place exponents, and finite-prime budget are unchanged.
-/

open Real Finset

namespace GRHSimplification.CommonMultiplierHeight

variable {I : Type*} (prime : I → Nat.Primes)
  {F : I → Type*} [∀ i, NormedField (F i)] (localMap : ∀ i, ℂ →+* F i)

/-- The common-multiplier height, with local normed fields left as parameters. -/
def HeightLe (c : ℝ) (y : I → ℂ) : Prop :=
  ∃ (H : ℂ) (α : ℝ) (h : ℕ → ℝ), H ≠ 0 ∧ (∀ l : ℕ, 0 ≤ h l) ∧
    (∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ exp α) ∧
    (∀ i : I, ‖localMap i (H * y i)‖ ≤ ((prime i : ℕ) : ℝ) ^ h (prime i)) ∧
    ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → α + ∑ l ∈ T, h l * log l ≤ c

namespace HeightLe

variable {prime localMap} {c : ℝ} {y : I → ℂ}

/-- Positive powers multiply the witness budget by the exponent. This is the
standalone counterpart of the source's existing `New.HeightLe.pow`. -/
theorem pow (hy : HeightLe prime localMap c y) (n : ℕ) :
    HeightLe prime localMap (n * c) (y ^ n) := by
  obtain ⟨H, α, h, hH, hh, hα, hlocal, hbudget⟩ := hy
  refine ⟨H ^ n, n * α, fun l ↦ n * h l, pow_ne_zero _ hH,
    fun l ↦ mul_nonneg (Nat.cast_nonneg n) (hh l), ?_, ?_, ?_⟩
  · intro σ
    simpa [map_pow, norm_pow, exp_nat_mul] using
      pow_le_pow_left₀ (norm_nonneg _) (hα σ) n
  · intro i
    calc
      ‖localMap i (H ^ n * (y ^ n) i)‖ = ‖localMap i (H * y i)‖ ^ n := by
        simp [map_mul, map_pow, norm_mul, norm_pow, mul_pow]
      _ ≤ (((prime i : ℕ) : ℝ) ^ h (prime i)) ^ n :=
        pow_le_pow_left₀ (norm_nonneg _) (hlocal i) n
      _ = ((prime i : ℕ) : ℝ) ^ (n * h (prime i)) := by
        rw [mul_comm (n : ℝ), Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  · intro T hT
    calc
      n * α + ∑ l ∈ T, n * h l * log l = n * (α + ∑ l ∈ T, h l * log l) := by
        simp only [mul_add, Finset.mul_sum, mul_assoc]
      _ ≤ n * c := mul_le_mul_of_nonneg_left (hbudget T hT) (Nat.cast_nonneg n)

/-- Taking a positive integral root divides the entire height budget by its degree.
No nonvanishing assumption on the family `y` is required. -/
theorem of_pow {n : ℕ} (hn : 0 < n)
    (hy : HeightLe prime localMap c (y ^ n)) :
    HeightLe prime localMap (c / n) y := by
  obtain ⟨H, α, h, hH, hh, hα, hlocal, hbudget⟩ := hy
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  let K : ℂ := H ^ ((n : ℂ)⁻¹)
  have hKpow : K ^ n = H := Complex.cpow_nat_inv_pow H hn0
  have hK : K ≠ 0 := by
    intro hz
    apply hH
    rw [← hKpow, hz, zero_pow hn0]
  refine ⟨K, α / n, fun l ↦ h l / n, hK,
    fun l ↦ div_nonneg (hh l) (Nat.cast_nonneg n), ?_, ?_, ?_⟩
  · intro σ
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (exp_nonneg _) hn0).mp
    calc
      ‖σ K‖ ^ n = ‖σ H‖ := by rw [← norm_pow, ← map_pow, hKpow]
      _ ≤ exp α := hα σ
      _ = exp (α / n) ^ n := by
        rw [← exp_nat_mul]
        congr 1
        field_simp
  · intro i
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hn0).mp
    calc
      ‖localMap i (K * y i)‖ ^ n = ‖localMap i (H * (y ^ n) i)‖ := by
        rw [← norm_pow, ← map_pow, mul_pow, hKpow]
        rfl
      _ ≤ ((prime i : ℕ) : ℝ) ^ h (prime i) := hlocal i
      _ = (((prime i : ℕ) : ℝ) ^ (h (prime i) / n)) ^ n := by
        rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
        congr 1
        field_simp
  · intro T hT
    calc
      α / n + ∑ l ∈ T, h l / n * log l =
          (α + ∑ l ∈ T, h l * log l) / n := by
        simp only [add_div, Finset.sum_div]
        congr 1
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ ≤ c / n := div_le_div_of_nonneg_right (hbudget T hT) (Nat.cast_nonneg n)

/-- Exact homogeneity in the form useful when a squared recurrence gives the
budget first. -/
theorem pow_iff {n : ℕ} (hn : 0 < n) :
    HeightLe prime localMap c (y ^ n) ↔ HeightLe prime localMap (c / n) y := by
  constructor
  · exact of_pow hn
  · intro hy
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hcancel : (n : ℝ) * (c / n) = c := by field_simp
    simpa only [hcancel] using hy.pow n

/-- The same equivalence with the budget written as `n * c`. -/
theorem scaled_pow_iff {n : ℕ} (hn : 0 < n) :
    HeightLe prime localMap (n * c) (y ^ n) ↔ HeightLe prime localMap c y := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hcancel : ((n : ℝ) * c) / n = c := by field_simp
  simpa only [hcancel] using (pow_iff (prime := prime) (localMap := localMap)
    (c := n * c) (y := y) hn)

/-- A square recurrence carries exactly twice the unsquared height budget. -/
theorem sq_iff :
    HeightLe prime localMap (2 * c) (y ^ 2) ↔ HeightLe prime localMap c y := by
  simpa using (scaled_pow_iff (prime := prime) (localMap := localMap)
    (c := c) (y := y) (n := 2) (by decide))

-- Consumer-shaped smoke application: no pointwise nonzero hypothesis is needed.
example (hy : HeightLe prime localMap (2 * c) (fun i ↦ y i ^ 2)) :
    HeightLe prime localMap c y :=
  sq_iff.mp hy

-- A second application checks the unscaled budget and a nontrivial exponent.
example (hy : HeightLe prime localMap c (y ^ 3)) :
    HeightLe prime localMap (c / 3) y :=
  of_pow (by decide : 0 < 3) hy

#print axioms pow
#print axioms of_pow
#print axioms pow_iff
#print axioms scaled_pow_iff
#print axioms sq_iff

end HeightLe
end GRHSimplification.CommonMultiplierHeight
