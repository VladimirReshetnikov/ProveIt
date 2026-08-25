import FabiusFunction.GlobalBounds

/-!
# Iterated derivatives of the bounded Fabius function

`FabiusFunction.GlobalExtension` proves equation (3) for the signed extension
and `FabiusFunction.GlobalBounds` turns it into the sharp uniform bound
`2^C(k+1,2)`.  Both are stated for `extendedFabius`.  This file transfers them
to the bounded, CDF-style `fabiusReal`.

The bridge is that the two functions have the same germ at every argument
below one — they both vanish on `(-∞, 0]` and they agree on `[0,1]` — so
equation (3) holds verbatim for `fabiusReal` on `(-∞, 1)`.  Above one the
bounded function is locally constant, so every positive-order derivative
vanishes; the remaining point `x = 1` is caught by continuity, because the set
where a continuous function is bounded by a constant is closed and `Iic 1` is
the closure of `Iio 1`.

Two consequences are worth naming separately: `fabiusReal` is flat at the
origin (every derivative vanishes there, since `extendedFabius 0 = 0`), and
`2^C(k+1,2)` is the exact, attained supremum of `|F^(k)|`.
-/

set_option autoImplicit false

open scoped ContDiff
open Set

namespace Fabius

/-- The bounded function and the signed extension agree on `(-∞, 1]`: both
vanish on `(-∞, 0]` and they agree on the unit interval. -/
theorem fabiusReal_eq_extendedFabius_of_le_one (F : BoundedFabius)
    (hF : IsFabius F) {y : ℝ} (hy : y ≤ 1) :
    fabiusReal F y = extendedFabius F y := by
  by_cases hy0 : y ≤ 0
  · rw [extendedFabius_eq_zero_of_nonpos F hF hy0, hF.zero_of_nonpos y hy0]
  · exact (extendedFabius_eq_fabiusReal F hF
      ⟨le_of_lt (lt_of_not_ge hy0), hy⟩).symm

/-- Equation (3) for the bounded Fabius function, at every argument below one. -/
theorem iteratedDeriv_fabiusReal_of_lt_one (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) {x : ℝ} (hx : x < 1) :
    iteratedDeriv k (fabiusReal F) x =
      2 ^ (k + 1).choose 2 * extendedFabius F (2 ^ k * x) := by
  have heq : fabiusReal F =ᶠ[nhds x] extendedFabius F := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact fabiusReal_eq_extendedFabius_of_le_one F hF (le_of_lt hy)
  rw [heq.iteratedDeriv_eq k, iteratedDeriv_extendedFabius F hF k x]

/-- The bounded Fabius function is flat at the origin: every derivative
vanishes there. -/
theorem iteratedDeriv_fabiusReal_zero (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) : iteratedDeriv k (fabiusReal F) 0 = 0 := by
  rw [iteratedDeriv_fabiusReal_of_lt_one F hF k (by norm_num), mul_zero,
    extendedFabius_eq_zero_of_nonpos F hF le_rfl, mul_zero]

private lemma iteratedDeriv_const_succ (c : ℝ) (m : ℕ) :
    iteratedDeriv (m + 1) (fun _ : ℝ => c) = fun _ => 0 := by
  induction m with
  | zero =>
      funext y
      rw [iteratedDeriv_one]
      simp
  | succ m ih =>
      funext y
      rw [iteratedDeriv_succ, ih]
      simp

/-- To the right of the unit interval the bounded Fabius function is locally
constant, so every positive-order derivative vanishes. -/
theorem iteratedDeriv_fabiusReal_eq_zero_of_one_lt (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) {x : ℝ} (hx : 1 < x) :
    iteratedDeriv (m + 1) (fabiusReal F) x = 0 := by
  have heq : fabiusReal F =ᶠ[nhds x] fun _ : ℝ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hF.one_of_one_le y (le_of_lt hy)
  rw [heq.iteratedDeriv_eq (m + 1), iteratedDeriv_const_succ]

/-- Sharp uniform bound for every iterated derivative of the bounded Fabius
function, valid at every real argument. -/
theorem abs_iteratedDeriv_fabiusReal_le (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (x : ℝ) :
    |iteratedDeriv k (fabiusReal F) x| ≤ 2 ^ (k + 1).choose 2 := by
  have hcont : Continuous (iteratedDeriv k (fabiusReal F)) :=
    hF.contDiff.continuous_iteratedDeriv k (by exact WithTop.coe_le_coe.mpr le_top)
  have hclosed :
      IsClosed {y : ℝ | |iteratedDeriv k (fabiusReal F) y| ≤
        2 ^ (k + 1).choose 2} :=
    isClosed_le hcont.abs continuous_const
  by_cases hx : x ≤ 1
  · have hsub : Iio (1 : ℝ) ⊆
        {y : ℝ | |iteratedDeriv k (fabiusReal F) y| ≤ 2 ^ (k + 1).choose 2} := by
      intro y hy
      show |iteratedDeriv k (fabiusReal F) y| ≤ 2 ^ (k + 1).choose 2
      rw [iteratedDeriv_fabiusReal_of_lt_one F hF k hy, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1).choose 2)]
      nlinarith [abs_extendedFabius_le_one F hF ((2 : ℝ) ^ k * y),
        abs_nonneg (extendedFabius F ((2 : ℝ) ^ k * y)),
        (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1).choose 2)]
    have hcl : Iic (1 : ℝ) ⊆
        {y : ℝ | |iteratedDeriv k (fabiusReal F) y| ≤ 2 ^ (k + 1).choose 2} := by
      rw [← closure_Iio (1 : ℝ)]
      exact hclosed.closure_subset_iff.mpr hsub
    exact hcl hx
  · push_neg at hx
    match k with
    | 0 =>
        have h1 : ((0 : ℕ) + 1).choose 2 = 0 := by decide
        rw [iteratedDeriv_zero, h1, pow_zero,
          abs_of_nonneg (fabiusReal_nonneg F x)]
        exact fabiusReal_le_one F x
    | (m + 1) =>
        rw [iteratedDeriv_fabiusReal_eq_zero_of_one_lt F hF m hx, abs_zero]
        positivity

/-- The uniform bound is attained at `2^(-k)`. -/
theorem iteratedDeriv_fabiusReal_inv_two_pow (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (hk : 1 ≤ k) :
    iteratedDeriv k (fabiusReal F) (((2 : ℝ) ^ k)⁻¹) = 2 ^ (k + 1).choose 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hone : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  have hps : (2 : ℝ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
  have hc : ((2 : ℝ) ^ (j + 1))⁻¹ * 2 ^ (j + 1) = 1 :=
    inv_mul_cancel₀ (ne_of_gt hpos)
  have hlt : ((2 : ℝ) ^ (j + 1))⁻¹ < 1 := by
    nlinarith [inv_pos.mpr hpos]
  rw [iteratedDeriv_fabiusReal_of_lt_one F hF (j + 1) hlt,
    mul_inv_cancel₀ (ne_of_gt hpos), extendedFabius_one F hF, mul_one]

/-- `2^C(k+1,2)` is exactly the supremum of the `k`-th derivative of the
bounded Fabius function in absolute value, and it is attained at `2^(-k)`. -/
theorem isGreatest_abs_iteratedDeriv_fabiusReal (F : BoundedFabius)
    (hF : IsFabius F) (k : ℕ) (hk : 1 ≤ k) :
    IsGreatest (Set.range fun x : ℝ => |iteratedDeriv k (fabiusReal F) x|)
      (2 ^ (k + 1).choose 2) := by
  constructor
  · refine ⟨((2 : ℝ) ^ k)⁻¹, ?_⟩
    show |iteratedDeriv k (fabiusReal F) (((2 : ℝ) ^ k)⁻¹)| =
      2 ^ (k + 1).choose 2
    rw [iteratedDeriv_fabiusReal_inv_two_pow F hF k hk,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1).choose 2)]
  · rintro y ⟨x, rfl⟩
    exact abs_iteratedDeriv_fabiusReal_le F hF k x

end Fabius
