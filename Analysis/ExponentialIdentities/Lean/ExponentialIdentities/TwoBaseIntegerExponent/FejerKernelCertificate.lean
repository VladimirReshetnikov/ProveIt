import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# A finite Fejér-kernel certificate for exact integer phases

This file formalizes the finite harmonic-analysis core of the probability continuation in
the Alaoglu--Erdős report.  For unit complex phases `z i`, it proves:

* positivity and normalization of the normalized Fejér kernel;
* the exact Fourier expansion, with frequency `h` occurring `H - h` times;
* the corresponding finite score identity in terms of exponential sums; and
* the positive-kernel bound saying that every exact integer phase contributes one.

The results are deliberately finite.  They do not assume equidistribution, a random-phase
model, or an unformalized exponential-sum estimate.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ## The normalized finite Fejér kernel -/

/-- The length-`H` geometric phase sum `1 + z + ⋯ + z^(H-1)`. -/
def geometricPhaseSum (H : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range H, z ^ j

/-- Adding one term at the right is equivalently the recurrence
`A_(n+1)(z) = 1 + z A_n(z)`. -/
theorem geometricPhaseSum_succ (n : ℕ) (z : ℂ) :
    geometricPhaseSum (n + 1) z = 1 + z * geometricPhaseSum n z := by
  rw [geometricPhaseSum, Finset.sum_range_succ']
  simp only [pow_succ']
  rw [← Finset.mul_sum]
  simp only [geometricPhaseSum, pow_zero]
  ac_rfl

/-- The real part of the cross term in the Fejér recurrence is the sum of the positive
frequencies `1, …, n`. -/
theorem mul_geometricPhaseSum_re (n : ℕ) (z : ℂ) :
    (z * geometricPhaseSum n z).re =
      ∑ h ∈ Finset.range n, (z ^ (h + 1)).re := by
  simp only [geometricPhaseSum, Finset.mul_sum, pow_succ']
  exact map_sum Complex.reCLM _ _

/-- A triangular sum groups by frequency with multiplicity `H - (h + 1)`.  The terminal
frequency in `range H` has coefficient zero; retaining it makes later formulas uniform. -/
theorem sum_sum_range_eq_weighted (H : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range H, ∑ h ∈ Finset.range n, f h) =
      ∑ h ∈ Finset.range H, ((H - (h + 1) : ℕ) : ℝ) * f h := by
  induction H with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have hzero : n + 1 - (n + 1) = 0 := by omega
      rw [hzero]
      norm_num
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h hh
      have hlt : h < n := Finset.mem_range.mp hh
      have hnat : n + 1 - (h + 1) = (n - (h + 1)) + 1 := by omega
      rw [hnat]
      push_cast
      ring

/-- The unnormalized Fourier numerator

`H + 2 ∑_{1 ≤ h < H} (H-h) Re(z^h)`.

It is written with a harmless final zero-weight term. -/
def fejerFourierNumerator (H : ℕ) (z : ℂ) : ℝ :=
  (H : ℝ) + 2 * ∑ h ∈ Finset.range H,
    ((H - (h + 1) : ℕ) : ℝ) * (z ^ (h + 1)).re

/-- On the unit circle, the squared geometric sum has the exact finite Fourier expansion. -/
theorem normSq_geometricPhaseSum_eq_fejerFourierNumerator
    (H : ℕ) (z : ℂ) (hz : Complex.normSq z = 1) :
    Complex.normSq (geometricPhaseSum H z) = fejerFourierNumerator H z := by
  induction H with
  | zero => simp [geometricPhaseSum, fejerFourierNumerator]
  | succ n ih =>
      rw [geometricPhaseSum_succ, Complex.normSq_add, Complex.normSq_one,
        Complex.normSq_mul, hz, one_mul, ih]
      have hcross : (1 * conj (z * geometricPhaseSum n z)).re =
          ∑ h ∈ Finset.range n, (z ^ (h + 1)).re := by
        rw [one_mul, Complex.conj_re, mul_geometricPhaseSum_re]
      rw [hcross]
      simp only [fejerFourierNumerator]
      rw [← sum_sum_range_eq_weighted n (fun h ↦ (z ^ (h + 1)).re)]
      rw [← sum_sum_range_eq_weighted (n + 1) (fun h ↦ (z ^ (h + 1)).re)]
      rw [Finset.sum_range_succ]
      push_cast
      ring

/-- The normalized Fejér kernel `|∑_{j < H} z^j|² / H²`. -/
def normalizedFejerKernel (H : ℕ) (z : ℂ) : ℝ :=
  Complex.normSq (geometricPhaseSum H z) / (H : ℝ) ^ 2

/-- Positivity of the normalized Fejér kernel. -/
theorem normalizedFejerKernel_nonneg (H : ℕ) (z : ℂ) :
    0 ≤ normalizedFejerKernel H z := by
  exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)

/-- At phase one, every summand is one and the normalized kernel is exactly one. -/
@[simp] theorem normalizedFejerKernel_one (H : ℕ) (hH : 0 < H) :
    normalizedFejerKernel H 1 = 1 := by
  simp only [normalizedFejerKernel, geometricPhaseSum, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Complex.normSq_natCast]
  have hHreal : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp

/-- Fourier form of the normalized kernel. -/
theorem normalizedFejerKernel_eq_fourier (H : ℕ) (z : ℂ)
    (hz : Complex.normSq z = 1) :
    normalizedFejerKernel H z = fejerFourierNumerator H z / (H : ℝ) ^ 2 := by
  rw [normalizedFejerKernel, normSq_geometricPhaseSum_eq_fejerFourierNumerator H z hz]

/-! ## Finite Fejér scores and exact-hit certificates -/

/-- The finite exponential sum at frequency `h`. -/
def phaseExponentialSum {I : Type*} [Fintype I] (z : I → ℂ) (h : ℕ) : ℂ :=
  ∑ i, z i ^ h

/-- The normalized Fejér score of a finite phase family. -/
def fejerScore {I : Type*} [Fintype I] (H : ℕ) (z : I → ℂ) : ℝ :=
  ∑ i, normalizedFejerKernel H (z i)

/-- **Positive-kernel exact-hit certificate.**  The number of phases equal to one is bounded
by their Fejér score.  This is the finite inequality `H_N ≤ Q_N(H)` from the report. -/
theorem exactPhaseHitCount_le_fejerScore {I : Type*} [Fintype I]
    (H : ℕ) (hH : 0 < H) (z : I → ℂ) :
    (((Finset.univ.filter fun i ↦ z i = 1).card : ℕ) : ℝ) ≤ fejerScore H z := by
  classical
  rw [← Finset.sum_boole (fun i ↦ z i = 1) Finset.univ]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs with hz
  · rw [hz, normalizedFejerKernel_one H hH]
  · exact normalizedFejerKernel_nonneg H (z i)

/-- **Exact finite Fourier score identity.**  For unit phases, the score is the random-phase
baseline `card I / H` plus the weighted positive-frequency contribution. -/
theorem fejerScore_eq_fourier {I : Type*} [Fintype I]
    (H : ℕ) (z : I → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1) :
    fejerScore H z =
      ((Fintype.card I : ℝ) * (H : ℝ) +
        2 * ∑ h ∈ Finset.range H,
          ((H - (h + 1) : ℕ) : ℝ) * (phaseExponentialSum z (h + 1)).re) /
        (H : ℝ) ^ 2 := by
  classical
  simp only [fejerScore, normalizedFejerKernel_eq_fourier H _ (hz _),
    fejerFourierNumerator]
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.mul_sum]
  congr 1
  simp only [phaseExponentialSum]
  simpa only [Complex.reCLM_apply] using
    (map_sum Complex.reCLM (fun i ↦ z i ^ (h + 1)) Finset.univ).symm

/-- The score identity separated into its `card I / H` baseline and weighted-frequency
correction. -/
theorem fejerScore_eq_card_div_add_weightedFrequencies {I : Type*} [Fintype I]
    (H : ℕ) (hH : 0 < H) (z : I → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1) :
    fejerScore H z =
      (Fintype.card I : ℝ) / H +
        2 / (H : ℝ) ^ 2 * ∑ h ∈ Finset.range H,
          ((H - (h + 1) : ℕ) : ℝ) * (phaseExponentialSum z (h + 1)).re := by
  rw [fejerScore_eq_fourier H z hz]
  have hHreal : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp

/-! ## Real phases and integer hits -/

/-- The standard circle phase `e(t) = exp(2πit)`. -/
def circlePhase (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))

/-- Every standard circle phase has norm squared one. -/
theorem normSq_circlePhase (t : ℝ) : Complex.normSq (circlePhase t) = 1 := by
  rw [circlePhase, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  norm_num

/-- Powers of a circle phase are exactly the corresponding integer frequencies. -/
theorem circlePhase_pow (t : ℝ) (h : ℕ) :
    circlePhase t ^ h = circlePhase ((h : ℝ) * t) := by
  rw [circlePhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Thus the abstract finite exponential sum specializes to `∑_i e(h t_i)`. -/
theorem phaseExponentialSum_circlePhase {I : Type*} [Fintype I]
    (t : I → ℝ) (h : ℕ) :
    phaseExponentialSum (fun i ↦ circlePhase (t i)) h =
      ∑ i, circlePhase ((h : ℝ) * t i) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact circlePhase_pow (t i) h

/-- Integer real phases map to one. -/
theorem circlePhase_intCast (n : ℤ) : circlePhase (n : ℝ) = 1 := by
  simpa only [circlePhase, Complex.ofReal_intCast] using
    Complex.exp_int_mul_two_pi_mul_I n

/-- The standard circle phase equals one exactly at integer real phases. -/
theorem circlePhase_eq_one_iff (t : ℝ) :
    circlePhase t = 1 ↔ ∃ n : ℤ, t = n := by
  rw [circlePhase, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hfactor : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      apply mul_ne_zero
      · norm_num [Real.pi_ne_zero]
      · exact Complex.I_ne_zero
    have hcast : (t : ℂ) = (n : ℂ) := by
      exact mul_right_cancel₀ hfactor hn
    exact_mod_cast hcast
  · rintro ⟨n, rfl⟩
    exact ⟨n, rfl⟩

/-- The indices whose real phases are exact integers. -/
noncomputable def exactIntegerPhaseIndices {I : Type*} [Fintype I]
    (t : I → ℝ) : Finset I := by
  classical
  exact Finset.univ.filter fun i ↦ ∃ n : ℤ, t i = n

/-- Exact integer phases are bounded by the Fejér score of their circle phases. -/
theorem exactIntegerPhaseCount_le_fejerScore {I : Type*} [Fintype I]
    (H : ℕ) (hH : 0 < H) (t : I → ℝ) :
    (exactIntegerPhaseIndices t).card ≤
      fejerScore H (fun i ↦ circlePhase (t i)) := by
  classical
  simpa only [exactIntegerPhaseIndices, circlePhase_eq_one_iff] using
    exactPhaseHitCount_le_fejerScore H hH (fun i ↦ circlePhase (t i))

end

end LeanProofs.TwoBaseIntegerExponent
