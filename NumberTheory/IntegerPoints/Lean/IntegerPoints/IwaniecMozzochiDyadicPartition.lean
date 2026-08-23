import IntegerPoints.IwaniecMozzochi
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A canonical dyadic partition and the Iwaniec--Mozzochi identity

Mathlib's smooth transition function gives a concrete witness for the smooth
partition assumed throughout the paper.  If

`g(t) = smoothTransition ((4 - t) / 2)`,

then `g = 1` on `(-∞,2]` and `g = 0` on `[4,∞)`.  The telescoping
difference `chi(t) = g(t) - g(2t)` satisfies all clauses of
`IsDyadicPartition` globally, without any piecewise smoothness argument.

The support conditions in `IsDyadicPartition` make the sum in (3.1) genuinely
finite.  For `x > 0`, choose `n : ℤ` with `2^n < x ≤ 2^(n+1)`.  Only the
indices `n - 1` and `n` can contribute, and the defining relation
`chi(t) = 1 - chi(2t)` makes those two terms add to one.
-/

open scoped BigOperators
open Real Finset Set

namespace LeanProofs.IntegerPoints

/-! ## A concrete smooth dyadic partition -/

private noncomputable def dyadicCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition ((4 - t) / 2)

/-- A canonical smooth dyadic partition obtained as a telescoping difference
of two rescaled smooth cutoffs. -/
noncomputable def canonicalDyadicPartition (t : ℝ) : ℝ :=
  dyadicCutoff t - dyadicCutoff (2 * t)

private theorem dyadicCutoff_one_of_le_two {t : ℝ} (ht : t ≤ 2) :
    dyadicCutoff t = 1 := by
  unfold dyadicCutoff
  exact Real.smoothTransition.one_of_one_le (by linarith)

private theorem dyadicCutoff_zero_of_four_le {t : ℝ} (ht : 4 ≤ t) :
    dyadicCutoff t = 0 := by
  unfold dyadicCutoff
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem dyadicCutoff_pos_of_lt_four {t : ℝ} (ht : t < 4) :
    0 < dyadicCutoff t := by
  unfold dyadicCutoff
  exact Real.smoothTransition.pos_of_pos (by linarith)

private theorem dyadicCutoff_le_one (t : ℝ) : dyadicCutoff t ≤ 1 := by
  exact Real.smoothTransition.le_one _

/-- The canonical telescoping cutoff satisfies every smoothness, support,
positivity, and recurrence clause required by `IsDyadicPartition`. -/
theorem canonicalDyadicPartition_isDyadicPartition :
    IsDyadicPartition canonicalDyadicPartition := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold canonicalDyadicPartition dyadicCutoff
    fun_prop
  · intro t ht
    change dyadicCutoff t - dyadicCutoff (2 * t) = 0
    rw [dyadicCutoff_zero_of_four_le ht,
      dyadicCutoff_zero_of_four_le (t := 2 * t) (by linarith)]
    norm_num
  · intro t _ht2 ht4
    change 0 < dyadicCutoff t - dyadicCutoff (2 * t) ∧
      dyadicCutoff t - dyadicCutoff (2 * t) ≤ 1
    rw [dyadicCutoff_zero_of_four_le (t := 2 * t) (by linarith)]
    simpa using
      ⟨dyadicCutoff_pos_of_lt_four ht4, dyadicCutoff_le_one t⟩
  · intro t _ht1 ht2
    change dyadicCutoff t - dyadicCutoff (2 * t) =
      1 - (dyadicCutoff (2 * t) - dyadicCutoff (2 * (2 * t)))
    rw [dyadicCutoff_one_of_le_two ht2,
      dyadicCutoff_zero_of_four_le (t := 2 * (2 * t)) (by linarith)]
    ring
  · intro t ht
    change dyadicCutoff t - dyadicCutoff (2 * t) = 0
    rw [dyadicCutoff_one_of_le_two (t := t) (by linarith),
      dyadicCutoff_one_of_le_two (t := 2 * t) (by linarith)]
    norm_num

/-- There exists a smooth dyadic partition satisfying the exact assumptions
used by the Iwaniec--Mozzochi development. -/
theorem exists_isDyadicPartition : ∃ χ : ℝ → ℝ, IsDyadicPartition χ :=
  ⟨canonicalDyadicPartition, canonicalDyadicPartition_isDyadicPartition⟩

/-! ## The partition-of-unity identity -/

private theorem eq31_prev_argument (x : ℝ) (n : ℤ) :
    x / (2 : ℝ) ^ (n - 1) = 2 * (x / (2 : ℝ) ^ n) := by
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hpow : (2 : ℝ) ^ n ≠ 0 := zpow_ne_zero n htwo
  rw [zpow_sub₀ htwo n 1, zpow_one]
  field_simp [hpow]

private theorem eq31_four_mul_zpow (j : ℤ) :
    (4 : ℝ) * (2 : ℝ) ^ j = (2 : ℝ) ^ (j + 2) := by
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  calc
    (4 : ℝ) * (2 : ℝ) ^ j = (2 : ℝ) ^ (2 : ℤ) * (2 : ℝ) ^ j := by norm_num
    _ = (2 : ℝ) ^ ((2 : ℤ) + j) := (zpow_add₀ htwo 2 j).symm
    _ = (2 : ℝ) ^ (j + 2) := by
      congr 1
      omega

/-- **Iwaniec--Mozzochi (3.1).**  The dyadic translates of `chi` form a
partition of unity on the positive real axis. -/
theorem iwaniecMozzochi_eq31_holds : iwaniecMozzochi_eq31 := by
  intro χ hχ x hx
  rcases hχ with ⟨_, hχhigh, _, hχrecur, hχlow⟩
  obtain ⟨n, hnLower, hnUpper⟩ :=
    exists_mem_Ioc_zpow hx (by norm_num : (1 : ℝ) < 2)
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have htwoOne : (1 : ℝ) ≤ 2 := by norm_num
  have hpowPos (j : ℤ) : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j

  have htLower : 1 < x / (2 : ℝ) ^ n := by
    rw [lt_div_iff₀ (hpowPos n)]
    simpa only [one_mul] using hnLower
  have htUpper : x / (2 : ℝ) ^ n ≤ 2 := by
    rw [div_le_iff₀ (hpowPos n)]
    calc
      x ≤ (2 : ℝ) ^ (n + 1) := hnUpper
      _ = (2 : ℝ) ^ n * 2 := zpow_add_one₀ htwo n
      _ = 2 * (2 : ℝ) ^ n := by ring
  have hpair :
      χ (x / (2 : ℝ) ^ (n - 1)) + χ (x / (2 : ℝ) ^ n) = 1 := by
    rw [eq31_prev_argument]
    rw [hχrecur (x / (2 : ℝ) ^ n) htLower htUpper]
    ring

  have hsupp :
      Function.support (fun j : ℤ => χ (x / (2 : ℝ) ^ j)) ⊆
        (↑({n - 1, n} : Finset ℤ) : Set ℤ) := by
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hjpair
    push Not at hjpair
    rcases hjpair with ⟨hjPrev, hjN⟩
    rcases lt_trichotomy j n with hjn | hjn | hnj
    · have hjexp : j + 2 ≤ n := by omega
      have hpowBound : (4 : ℝ) * (2 : ℝ) ^ j ≤ (2 : ℝ) ^ n := by
        rw [eq31_four_mul_zpow]
        exact zpow_le_zpow_right₀ htwoOne hjexp
      have harg : 4 ≤ x / (2 : ℝ) ^ j := by
        rw [le_div_iff₀ (hpowPos j)]
        exact hpowBound.trans hnLower.le
      exact hj (hχhigh _ harg)
    · subst j
      exact (hjN rfl).elim
    · have hjexp : n + 1 ≤ j := by omega
      have hpowBound : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ j :=
        zpow_le_zpow_right₀ htwoOne hjexp
      have hxpow : x ≤ (2 : ℝ) ^ j := hnUpper.trans hpowBound
      have harg : x / (2 : ℝ) ^ j ≤ 1 := (div_le_one (hpowPos j)).2 hxpow
      exact hj (hχlow _ harg)

  calc
    ∑ᶠ j : ℤ, χ (x / (2 : ℝ) ^ j) =
        ∑ j ∈ ({n - 1, n} : Finset ℤ), χ (x / (2 : ℝ) ^ j) :=
      finsum_eq_sum_of_support_subset _ hsupp
    _ = χ (x / (2 : ℝ) ^ (n - 1)) + χ (x / (2 : ℝ) ^ n) := by
      have hne : n - 1 ≠ n := by omega
      simp [hne]
    _ = 1 := hpair

end LeanProofs.IntegerPoints
