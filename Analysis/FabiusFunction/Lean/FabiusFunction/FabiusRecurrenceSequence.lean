import FabiusFunction.FabiusDyadicLogBounds
import FabiusFunction.NegativeLaplaceVertical
import FabiusFunction.BernoulliRecurrences

/-!
# The recurrence sequence attached to the Fabius function

The sequence called `a_n` in the linked recurrence discussion is the
factorially normalized half-moment sequence

`a_n = halfMoment n / n!`.

This module records its displayed elementary recurrence, its exact relation
to `F(2⁻ⁿ)`, the Bernoulli-number recurrence from the generating-function
argument, and the corresponding entire series and dyadic product.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-- The sequence `a_n = d_n / n!` from the recurrence discussion, where
`d_n = halfMoment n`. -/
def fabiusRecurrenceSequence (n : ℕ) : ℚ :=
  halfMoment n / (n.factorial : ℚ)

/-- The initial value `a₀ = 1`, since `halfMoment 0 = 1` and `0! = 1`. -/
@[simp]
theorem fabiusRecurrenceSequence_zero : fabiusRecurrenceSequence 0 = 1 := by
  norm_num [fabiusRecurrenceSequence, halfMoment]

/-- Every term of the recurrence sequence is positive. -/
theorem fabiusRecurrenceSequence_pos (n : ℕ) :
    0 < fabiusRecurrenceSequence n := by
  exact div_pos (halfMoment_pos n) (by positivity)

/-- The exact rational factorial majorant behind the
faster-than-exponential decay. -/
theorem fabiusRecurrenceSequence_le_inv_factorial (n : ℕ) :
    fabiusRecurrenceSequence n ≤ ((n.factorial : ℚ))⁻¹ := by
  cases n with
  | zero => norm_num [fabiusRecurrenceSequence, halfMoment]
  | succ n =>
      simp only [fabiusRecurrenceSequence]
      rw [div_le_iff₀ (by positivity)]
      have hfac : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
      rw [inv_mul_cancel₀ hfac]
      exact_mod_cast halfMoment_real_le_one fabius fabius_spec (n + 1) (by omega)

/-- The factorial majorant after embedding the recurrence sequence in the
reals. -/
theorem fabiusRecurrenceSequence_cast_le_inv_factorial (n : ℕ) :
    (fabiusRecurrenceSequence n : ℝ) ≤ ((n.factorial : ℝ))⁻¹ := by
  rw [← Rat.cast_natCast, ← Rat.cast_inv_of_ne_zero, Rat.cast_le]
  · exact fabiusRecurrenceSequence_le_inv_factorial n
  · positivity

/-- In particular, `a_n` decays faster than every exponential: multiplying
it by `c^n`, for any fixed real `c`, still gives a sequence tending to zero. -/
theorem fabiusRecurrenceSequence_faster_than_exponential (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => c ^ n * (fabiusRecurrenceSequence n : ℝ))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm
    (a := fun n : ℕ => |c| ^ n / (n.factorial : ℝ))
  intro n
  have hpos : 0 < (fabiusRecurrenceSequence n : ℝ) := by
    exact_mod_cast fabiusRecurrenceSequence_pos n
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hpos]
  calc
    |c| ^ n * (fabiusRecurrenceSequence n : ℝ) ≤
        |c| ^ n * ((n.factorial : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left
        (fabiusRecurrenceSequence_cast_le_inv_factorial n)
        (pow_nonneg (abs_nonneg c) n)
    _ = |c| ^ n / (n.factorial : ℝ) := by rw [div_eq_mul_inv]
  exact FloorSemiring.tendsto_pow_div_factorial_atTop |c|

/-- The ordinary complex power series of the recurrence sequence converges
absolutely at every point. -/
theorem summable_norm_fabiusRecurrenceSequence_series (z : ℂ) :
    Summable (fun n : ℕ => ‖(fabiusRecurrenceSequence n : ℂ) * z ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (NormedSpace.norm_expSeries_div_summable z)
  rw [norm_mul, norm_pow, norm_div, norm_pow]
  have hpos : 0 < (fabiusRecurrenceSequence n : ℝ) := by
    exact_mod_cast fabiusRecurrenceSequence_pos n
  have hbound := fabiusRecurrenceSequence_cast_le_inv_factorial n
  rw [Complex.norm_ratCast, abs_of_pos hpos, Complex.norm_natCast]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_right hbound (pow_nonneg (norm_nonneg z) n)

/-- The ordinary complex power series of the recurrence sequence is summable
at every point. -/
theorem summable_fabiusRecurrenceSequence_series (z : ℂ) :
    Summable (fun n : ℕ => (fabiusRecurrenceSequence n : ℂ) * z ^ n) :=
  Summable.of_norm (summable_norm_fabiusRecurrenceSequence_series z)

/-- Successor-index form of the elementary recurrence for `a_n`. -/
theorem fabiusRecurrenceSequence_succ_recurrence (n : ℕ) :
    fabiusRecurrenceSequence (n + 1) =
      (∑ k : Fin (n + 1),
          fabiusRecurrenceSequence k /
            (((n + 2 - k : ℕ).factorial : ℕ) : ℚ)) /
        ((2 : ℚ) ^ (n + 1) - 1) := by
  rw [fabiusRecurrenceSequence, halfMoment_succ]
  calc
    ((∑ k : Fin (n + 1),
          (Nat.choose (n + 2) k.val : ℚ) * halfMoment k.val) /
          (((n + 2 : ℕ) : ℚ) * ((2 : ℚ) ^ (n + 1) - 1))) /
        (((n + 1).factorial : ℕ) : ℚ) =
      (∑ k : Fin (n + 1),
          ((Nat.choose (n + 2) k.val : ℚ) * halfMoment k.val) /
            (((n + 2 : ℕ) : ℚ) *
              (((n + 1).factorial : ℕ) : ℚ))) /
        ((2 : ℚ) ^ (n + 1) - 1) := by
          rw [← Finset.sum_div]
          have hn2 : (((n + 2 : ℕ) : ℚ)) ≠ 0 := by positivity
          have hfac : ((((n + 1).factorial : ℕ) : ℚ)) ≠ 0 := by
            positivity
          have hpow : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := by
            exact ne_of_gt (sub_pos.mpr
              (one_lt_pow₀ (a := (2 : ℚ)) (by norm_num) (by omega)))
          field_simp
    _ =
      (∑ k : Fin (n + 1),
          (halfMoment k.val / ((k.val.factorial : ℕ) : ℚ)) /
            (((n + 2 - k.val : ℕ).factorial : ℕ) : ℚ)) /
        ((2 : ℚ) ^ (n + 1) - 1) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _hk
          have hk : k.val ≤ n + 2 := by omega
          rw [Nat.cast_choose ℚ hk]
          rw [Nat.factorial_succ]
          field_simp
          push_cast
          ring

/-- The recurrence displayed in the source:

`a_n = (sum k < n, a_k / (n-k+1)!) / (2^n - 1)` for `n ≥ 1`.
-/
theorem fabiusRecurrenceSequence_recurrence (n : ℕ) (hn : 1 ≤ n) :
    fabiusRecurrenceSequence n =
      (∑ k ∈ range n,
          fabiusRecurrenceSequence k /
            (((n - k + 1).factorial : ℕ) : ℚ)) /
        ((2 : ℚ) ^ n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 1 m]
  rw [fabiusRecurrenceSequence_succ_recurrence]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => fabiusRecurrenceSequence k /
      (((m + 2 - k).factorial : ℕ) : ℚ)) (m + 1)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < m + 1 := mem_range.1 hk
  congr 3
  omega

/-- The exact rational dyadic value in terms of the recurrence sequence. -/
theorem halfMomentFabiusValue_eq_fabiusRecurrenceSequence (n : ℕ) :
    halfMomentFabiusValue n =
      ((2 : ℚ) ^ n.choose 2)⁻¹ * fabiusRecurrenceSequence n := by
  rw [halfMomentFabiusValue, fabiusRecurrenceSequence]
  field_simp

/-- The source identity `F(2⁻ⁿ) = (2^(choose n 2))⁻¹ a_n`. -/
theorem fabius_inverse_two_pow_eq_recurrenceSequence
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F (((2 : ℝ) ^ n)⁻¹) =
      ((2 : ℝ) ^ n.choose 2)⁻¹ * (fabiusRecurrenceSequence n : ℝ) := by
  simp only [fabiusRecurrenceSequence]
  push_cast
  rw [halfMoment_eq_fabius_formula F hF n]
  field_simp

/-- The exact rational inverse-power value in the recurrence-sequence
normalization. -/
theorem fabiusAtInverseTwoPow_eq_recurrenceSequence (n : ℕ) :
    fabiusAtInverseTwoPow n =
      ((2 : ℚ) ^ n.choose 2)⁻¹ * fabiusRecurrenceSequence n := by
  rw [fabiusAtInverseTwoPow_eq_halfMoment,
    halfMomentFabiusValue_eq_fabiusRecurrenceSequence]

/-- Exact rational form of the inverse-dyadic Fabius recurrence. -/
theorem fabiusAtInverseTwoPow_recurrence
    (n : ℕ) (hn : 1 ≤ n) :
    fabiusAtInverseTwoPow n =
      (((2 : ℚ) ^ n.choose 2)⁻¹ / ((2 : ℚ) ^ n - 1)) *
        ∑ k ∈ range n,
          ((2 : ℚ) ^ k.choose 2 /
              (((n - k + 1).factorial : ℕ) : ℚ)) *
            fabiusAtInverseTwoPow k := by
  have hsum :
      (∑ k ∈ range n,
          fabiusRecurrenceSequence k /
            (((n - k + 1).factorial : ℕ) : ℚ)) =
        ∑ k ∈ range n,
          ((2 : ℚ) ^ k.choose 2 /
              (((n - k + 1).factorial : ℕ) : ℚ)) *
            fabiusAtInverseTwoPow k := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [fabiusAtInverseTwoPow_eq_recurrenceSequence]
    have hpow : (2 : ℚ) ^ k.choose 2 ≠ 0 := by positivity
    have hfac : ((((n - k + 1).factorial : ℕ) : ℚ)) ≠ 0 := by
      positivity
    field_simp
  rw [fabiusAtInverseTwoPow_eq_recurrenceSequence,
    fabiusRecurrenceSequence_recurrence n hn, hsum]
  ring

/-- Exact rational form with the literal negative exponent from the displayed
recurrence. -/
theorem fabiusAtInverseTwoPow_recurrence_zpow
    (n : ℕ) (hn : 1 ≤ n) :
    fabiusAtInverseTwoPow n =
      ((2 : ℚ) ^ (-(n.choose 2 : ℤ)) / ((2 : ℚ) ^ n - 1)) *
        ∑ k ∈ range n,
          ((2 : ℚ) ^ k.choose 2 /
              (((n - k + 1).factorial : ℕ) : ℚ)) *
            fabiusAtInverseTwoPow k := by
  simpa [zpow_neg] using fabiusAtInverseTwoPow_recurrence n hn

/-- Generic real form of the inverse-dyadic recurrence for any bounded Fabius
function. -/
theorem fabiusFunction_inverse_two_pow_recurrence
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    fabiusReal F (((2 : ℝ) ^ n)⁻¹) =
      (((2 : ℝ) ^ n.choose 2)⁻¹ / ((2 : ℝ) ^ n - 1)) *
        ∑ k ∈ range n,
          ((2 : ℝ) ^ k.choose 2 /
              (((n - k + 1).factorial : ℕ) : ℝ)) *
            fabiusReal F (((2 : ℝ) ^ k)⁻¹) := by
  have hsum :
      (∑ k ∈ range n,
          (fabiusRecurrenceSequence k : ℝ) /
            (((n - k + 1).factorial : ℕ) : ℝ)) =
        ∑ k ∈ range n,
          ((2 : ℝ) ^ k.choose 2 /
              (((n - k + 1).factorial : ℕ) : ℝ)) *
            fabiusReal F (((2 : ℝ) ^ k)⁻¹) := by
    apply Finset.sum_congr rfl
    intro k _hk
    rw [fabius_inverse_two_pow_eq_recurrenceSequence F hF k]
    have hpow : (2 : ℝ) ^ k.choose 2 ≠ 0 := by positivity
    have hfac : ((((n - k + 1).factorial : ℕ) : ℝ)) ≠ 0 := by
      positivity
    field_simp
  rw [fabius_inverse_two_pow_eq_recurrenceSequence F hF n]
  have hrec := congrArg ((↑) : ℚ → ℝ)
    (fabiusRecurrenceSequence_recurrence n hn)
  push_cast at hrec
  rw [hrec, hsum]
  ring

/-- Generic real form matching the literal `2^(-n)` notation and factor order
in the displayed recurrence. -/
theorem fabiusFunction_inverse_two_pow_recurrence_zpow
    (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (hn : 1 ≤ n) :
    fabiusReal F ((2 : ℝ) ^ (-(n : ℤ))) =
      ((2 : ℝ) ^ (-(n.choose 2 : ℤ)) / ((2 : ℝ) ^ n - 1)) *
        ∑ k ∈ range n,
          ((2 : ℝ) ^ k.choose 2 /
              (((n - k + 1).factorial : ℕ) : ℝ)) *
            fabiusReal F ((2 : ℝ) ^ (-(k : ℤ))) := by
  simpa [zpow_neg] using
    fabiusFunction_inverse_two_pow_recurrence F hF n hn

/-- Canonical real form of the inverse-dyadic recurrence. -/
theorem fabius_inverse_two_pow_recurrence
    (n : ℕ) (hn : 1 ≤ n) :
    fabiusReal fabius (((2 : ℝ) ^ n)⁻¹) =
      (((2 : ℝ) ^ n.choose 2)⁻¹ / ((2 : ℝ) ^ n - 1)) *
        ∑ k ∈ range n,
          ((2 : ℝ) ^ k.choose 2 /
              (((n - k + 1).factorial : ℕ) : ℝ)) *
            fabiusReal fabius (((2 : ℝ) ^ k)⁻¹) :=
  fabiusFunction_inverse_two_pow_recurrence fabius fabius_spec n hn

/-- Canonical real form matching the literal `2^(-n)` notation in the
displayed recurrence. -/
theorem fabius_inverse_two_pow_recurrence_zpow
    (n : ℕ) (hn : 1 ≤ n) :
    fabiusReal fabius ((2 : ℝ) ^ (-(n : ℤ))) =
      ((2 : ℝ) ^ (-(n.choose 2 : ℤ)) / ((2 : ℝ) ^ n - 1)) *
        ∑ k ∈ range n,
          ((2 : ℝ) ^ k.choose 2 /
              (((n - k + 1).factorial : ℕ) : ℝ)) *
            fabiusReal fabius ((2 : ℝ) ^ (-(k : ℤ))) :=
  fabiusFunction_inverse_two_pow_recurrence_zpow fabius fabius_spec n hn

/-- Signed-global form of the displayed recurrence.  All arguments are in
`[0, 1]`, where the signed extension agrees with the bounded Fabius
function. -/
theorem globalFabius_inverse_two_pow_recurrence
    (n : ℕ) (hn : 1 ≤ n) :
    globalFabius ((2 : ℝ) ^ (-(n : ℤ))) =
      ((2 : ℝ) ^ (-(n.choose 2 : ℤ)) / ((2 : ℝ) ^ n - 1)) *
        ∑ k ∈ range n,
          ((2 : ℝ) ^ k.choose 2 /
              (((n - k + 1).factorial : ℕ) : ℝ)) *
            globalFabius ((2 : ℝ) ^ (-(k : ℤ))) := by
  have hlocal (k : ℕ) :
      globalFabius ((2 : ℝ) ^ (-(k : ℤ))) =
        fabiusReal fabius ((2 : ℝ) ^ (-(k : ℤ))) := by
    rw [globalFabius]
    apply extendedFabius_eq_fabiusReal fabius fabius_spec
    constructor
    · positivity
    · rw [zpow_neg]
      exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
  simp_rw [hlocal]
  exact fabius_inverse_two_pow_recurrence_zpow n hn

/-- The Bernoulli convolution before reflecting the finite sum. -/
theorem fabiusRecurrenceSequence_bernoulli_convolution (n : ℕ) :
    (∑ k ∈ range (n + 1),
        bernoulli k / ((k.factorial : ℕ) : ℚ) *
          (2 : ℚ) ^ (n - k) * fabiusRecurrenceSequence (n - k)) =
      fabiusRecurrenceSequence n := by
  have h := congrArg (fun q : ℚ => q / ((n.factorial : ℕ) : ℚ))
    (halfMoment_bernoulli_convolution n)
  rw [Finset.sum_div] at h
  simp only [fabiusRecurrenceSequence]
  rw [← h]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := Nat.le_of_lt_succ (mem_range.1 hk)
  rw [Nat.cast_choose ℚ hkle]
  field_simp

/-- The source-oriented Bernoulli recurrence

`a_n = sum k ≤ n, B_(n-k) 2^k a_k / (n-k)!`.
-/
theorem fabiusRecurrenceSequence_bernoulli_recurrence (n : ℕ) :
    fabiusRecurrenceSequence n =
      ∑ k ∈ range (n + 1),
        bernoulli (n - k) / (((n - k).factorial : ℕ) : ℚ) *
          (2 : ℚ) ^ k * fabiusRecurrenceSequence k := by
  rw [← fabiusRecurrenceSequence_bernoulli_convolution n]
  rw [← Finset.sum_range_reflect
    (fun k => bernoulli k / ((k.factorial : ℕ) : ℚ) *
      (2 : ℚ) ^ (n - k) * fabiusRecurrenceSequence (n - k)) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := Nat.le_of_lt_succ (mem_range.1 hk)
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hkle]

/-- The Bernoulli relation solved for the next recurrence-sequence term.
Unlike the source-oriented convolution, the right-hand side only uses earlier
terms.  The minus sign comes from moving the `B₀ 2ⁿ aₙ` self-term to the left. -/
theorem fabiusRecurrenceSequence_bernoulli_succ_recurrence (n : ℕ) :
    fabiusRecurrenceSequence (n + 1) =
      -(∑ k ∈ range (n + 1),
          bernoulli (n + 1 - k) /
              (((n + 1 - k).factorial : ℕ) : ℚ) *
            (2 : ℚ) ^ k * fabiusRecurrenceSequence k) /
        ((2 : ℚ) ^ (n + 1) - 1) := by
  have h := fabiusRecurrenceSequence_bernoulli_recurrence (n + 1)
  rw [sum_range_succ] at h
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one,
    div_one, bernoulli_zero, one_mul] at h
  have hpow : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr
      (one_lt_pow₀ (a := (2 : ℚ)) (by norm_num) (by omega)))
  rw [eq_div_iff hpow]
  linear_combination -h

/-- The Bernoulli relation solved for `aₙ`, retaining the positive-index
interface used by the other recurrence formulas. -/
theorem fabiusRecurrenceSequence_bernoulli_recurrence_isolated
    (n : ℕ) (hn : 1 ≤ n) :
    fabiusRecurrenceSequence n =
      -(∑ k ∈ range n,
          bernoulli (n - k) / (((n - k).factorial : ℕ) : ℚ) *
            (2 : ℚ) ^ k * fabiusRecurrenceSequence k) /
        ((2 : ℚ) ^ n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 1 m]
  exact fabiusRecurrenceSequence_bernoulli_succ_recurrence m

/-- The half-moment generating series is the ordinary generating series of
the factorially normalized recurrence sequence. -/
theorem halfMomentGeneratingSeries_eq_fabiusRecurrenceSequence_series
    (z : ℂ) :
    halfMomentGeneratingSeries z =
      ∑' n : ℕ, (fabiusRecurrenceSequence n : ℂ) * z ^ n := by
  apply tsum_congr
  intro n
  simp only [fabiusRecurrenceSequence]
  push_cast
  rfl

/-- The Fabius analytic generating function has coefficients `a_n`. -/
theorem complexGeneratingFunction_eq_fabiusRecurrenceSequence_series
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F z =
      ∑' n : ℕ, (fabiusRecurrenceSequence n : ℂ) * z ^ n := by
  rw [complexGeneratingFunction_eq_series F hF z]
  exact halfMomentGeneratingSeries_eq_fabiusRecurrenceSequence_series z

/-- `HasSum` form of the recurrence-sequence expansion of the analytic
generating function. -/
theorem hasSum_fabiusRecurrenceSequence_series
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    HasSum (fun n : ℕ => (fabiusRecurrenceSequence n : ℂ) * z ^ n)
      (complexGeneratingFunction F z) := by
  rw [complexGeneratingFunction_eq_fabiusRecurrenceSequence_series F hF z]
  exact (summable_fabiusRecurrenceSequence_series z).hasSum

/-- The alternating ordinary generating series of `a_n` is the canonical
dyadic product. -/
theorem fabiusRecurrenceSequence_series_neg_eq_tprod
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    (∑' n : ℕ, (fabiusRecurrenceSequence n : ℂ) * (-z) ^ n) =
      ∏' n : ℕ, negativeLaplaceDyadicFactor z n := by
  rw [← complexGeneratingFunction_eq_fabiusRecurrenceSequence_series F hF (-z)]
  exact complexGeneratingFunction_neg_eq_tprod F hF z

/-- `HasSum` form of the alternating recurrence-sequence product identity. -/
theorem hasSum_fabiusRecurrenceSequence_series_neg
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    HasSum (fun n : ℕ => (fabiusRecurrenceSequence n : ℂ) * (-z) ^ n)
      (∏' n : ℕ, negativeLaplaceDyadicFactor z n) := by
  rw [← fabiusRecurrenceSequence_series_neg_eq_tprod F hF z]
  exact (summable_fabiusRecurrenceSequence_series (-z)).hasSum

end

end Fabius
