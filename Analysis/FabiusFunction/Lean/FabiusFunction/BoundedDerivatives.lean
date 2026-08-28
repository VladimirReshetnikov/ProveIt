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

Three consequences are worth naming separately: `fabiusReal` is flat at the
origin (every derivative vanishes there, since `extendedFabius 0 = 0`); on
the matched dyadic grid its derivative values are a zero-interleaved,
sharply scaled Thue--Morse word; and `2^C(k+1,2)` is the exact, attained
supremum of `|F^(k)|`.
-/

set_option autoImplicit false

open scoped ContDiff
open Set

namespace Fabius

/-- Equation (3) for the bounded Fabius function, at every argument below one. -/
theorem iteratedDeriv_fabiusReal_of_lt_one (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) {x : ℝ} (hx : x < 1) :
    iteratedDeriv k (fabiusReal F) x =
      2 ^ (k + 1).choose 2 * extendedFabius F (2 ^ k * x) := by
  have heq : fabiusReal F =ᶠ[nhds x] extendedFabius F := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact fabiusReal_eq_extendedFabius_of_le_one F hF (le_of_lt hy)
  rw [heq.iteratedDeriv_eq k, iteratedDeriv_extendedFabius F hF k x]

/-- **Exact matched-dyadic derivative grid.**  On the mesh of spacing
`2⁻ᵏ`, the `k`-th derivative vanishes at every even numerator.  After
deleting those zeros, its values are the Thue--Morse word multiplied by the
sharp derivative amplitude `2 ^ C(k+1,2)`. -/
theorem iteratedDeriv_fabiusReal_dyadicGrid_eq_ite
    (F : BoundedFabius) (hF : IsFabius F)
    (k m : ℕ) (hm : m < 2 ^ k) :
    iteratedDeriv k (fabiusReal F) ((m : ℝ) / (2 : ℝ) ^ k) =
      if Even m then 0 else
        (thueMorseSign (m / 2) : ℝ) *
          (2 : ℝ) ^ (k + 1).choose 2 := by
  have hx : (m : ℝ) / (2 : ℝ) ^ k < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast hm
  rw [iteratedDeriv_fabiusReal_of_lt_one F hF k hx,
    show (2 : ℝ) ^ k * ((m : ℝ) / (2 : ℝ) ^ k) = (m : ℝ) by
      field_simp,
    extendedFabius_natCast_eq_ite F hF]
  by_cases heven : Even m
  · simp [heven]
  · simp [heven, thueMorseSign, mul_comm]

/-- A matched-grid jet vanishes exactly at an even numerator. -/
theorem iteratedDeriv_fabiusReal_dyadicGrid_eq_zero_iff
    (F : BoundedFabius) (hF : IsFabius F)
    (k m : ℕ) (hm : m < 2 ^ k) :
    iteratedDeriv k (fabiusReal F) ((m : ℝ) / (2 : ℝ) ^ k) = 0 ↔
      Even m := by
  rw [iteratedDeriv_fabiusReal_dyadicGrid_eq_ite F hF k m hm]
  by_cases heven : Even m <;> simp [heven, thueMorseSign]

/-- Every odd point of the matched dyadic grid attains the sharp derivative
supremum in absolute value. -/
theorem abs_iteratedDeriv_fabiusReal_dyadicGrid_of_odd
    (F : BoundedFabius) (hF : IsFabius F)
    (k m : ℕ) (hm : m < 2 ^ k) (hodd : Odd m) :
    |iteratedDeriv k (fabiusReal F) ((m : ℝ) / (2 : ℝ) ^ k)| =
      (2 : ℝ) ^ (k + 1).choose 2 := by
  rw [iteratedDeriv_fabiusReal_dyadicGrid_eq_ite F hF k m hm,
    if_neg (Nat.not_even_iff_odd.mpr hodd)]
  simp [thueMorseSign, abs_mul]

/-- The bounded Fabius function is flat at the origin: every derivative
vanishes there. -/
theorem iteratedDeriv_fabiusReal_zero (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) : iteratedDeriv k (fabiusReal F) 0 = 0 := by
  rw [iteratedDeriv_fabiusReal_of_lt_one F hF k (by norm_num), mul_zero,
    extendedFabius_eq_zero_of_nonpos F hF le_rfl, mul_zero]

/-- To the right of the unit interval the bounded Fabius function is locally
constant, so every positive-order derivative vanishes. -/
theorem iteratedDeriv_fabiusReal_eq_zero_of_one_lt (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) {x : ℝ} (hx : 1 < x) :
    iteratedDeriv (m + 1) (fabiusReal F) x = 0 := by
  have heq : fabiusReal F =ᶠ[nhds x] fun _ : ℝ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hF.one_of_one_le y (le_of_lt hy)
  exact (heq.iteratedDeriv_eq (m + 1)).trans (by simp [iteratedDeriv_const])

/-- Every positive-order derivative of the bounded Fabius function vanishes on
the whole closed ray `[1, ∞)`, the endpoint `x = 1` included.  The open ray is
`iteratedDeriv_fabiusReal_eq_zero_of_one_lt` (local constancy), and the
endpoint is caught by continuity, since the vanishing set of a continuous
function is closed and `Ici 1` is the closure of `Ioi 1`.

This is the right-endpoint mirror of `iteratedDeriv_fabiusReal_zero`, and the
pair is exactly the statement that `fabiusReal F` glues to its two constant
tails `0` and `1` in a `C^∞` fashion.  The strictly stronger hypothesis `1 < x`
of `iteratedDeriv_fabiusReal_eq_zero_of_one_lt` is deliberately kept there
rather than relaxed in place: the proof below consumes that lemma, so merging
the two would be circular. -/
theorem iteratedDeriv_fabiusReal_eq_zero_of_one_le (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    iteratedDeriv (m + 1) (fabiusReal F) x = 0 := by
  have hcont : Continuous (iteratedDeriv (m + 1) (fabiusReal F)) :=
    hF.contDiff.continuous_iteratedDeriv (m + 1)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (m + 1))
  have hclosed :
      IsClosed {y : ℝ | iteratedDeriv (m + 1) (fabiusReal F) y = 0} :=
    isClosed_eq hcont continuous_const
  have hsub : Ioi (1 : ℝ) ⊆
      {y : ℝ | iteratedDeriv (m + 1) (fabiusReal F) y = 0} := by
    intro y hy
    show iteratedDeriv (m + 1) (fabiusReal F) y = 0
    exact iteratedDeriv_fabiusReal_eq_zero_of_one_lt F hF m hy
  have hcl : Ici (1 : ℝ) ⊆
      {y : ℝ | iteratedDeriv (m + 1) (fabiusReal F) y = 0} := by
    rw [← closure_Ioi (1 : ℝ)]
    exact hclosed.closure_subset_iff.mpr hsub
  exact hcl hx

/-- Sharp uniform bound for every iterated derivative of the bounded Fabius
function, valid at every real argument. -/
theorem abs_iteratedDeriv_fabiusReal_le (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (x : ℝ) :
    |iteratedDeriv k (fabiusReal F) x| ≤ 2 ^ (k + 1).choose 2 := by
  have hcont : Continuous (iteratedDeriv k (fabiusReal F)) :=
    hF.contDiff.continuous_iteratedDeriv k
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
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
  · push Not at hx
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

/-- The uniform bound is attained at `2^(-k)`, for *every* order `k`, including
`k = 0`.  The order-zero case is not degenerate: `((2 : ℝ) ^ 0)⁻¹ = 1` and
`(0 + 1).choose 2 = 0`, so the statement reads `fabiusReal F 1 = 1`, which is
the constant right tail of the bounded Fabius function.  The hypothesis
`1 ≤ k` carried by `iteratedDeriv_fabiusReal_inv_two_pow` is therefore
unnecessary; that declaration is kept unchanged for compatibility, and the
positive-order case here is discharged by it. -/
theorem iteratedDeriv_fabiusReal_inv_two_pow_all (F : BoundedFabius)
    (hF : IsFabius F) (k : ℕ) :
    iteratedDeriv k (fabiusReal F) (((2 : ℝ) ^ k)⁻¹) = 2 ^ (k + 1).choose 2 := by
  match k with
  | 0 =>
      have h1 : ((0 : ℕ) + 1).choose 2 = 0 := by decide
      rw [iteratedDeriv_zero, pow_zero, inv_one, h1, pow_zero]
      exact hF.one_of_one_le 1 le_rfl
  | (j + 1) =>
      exact iteratedDeriv_fabiusReal_inv_two_pow F hF (j + 1) (by omega)

/-- `2^C(k+1,2)` is exactly the supremum of the `k`-th derivative of the
bounded Fabius function in absolute value, and it is attained at `2^(-k)` —
for *every* order `k`, including `k = 0`, where the statement says that the
supremum of `|fabiusReal F|` is `1`, attained at `1`.  This is the
hypothesis-free form of `isGreatest_abs_iteratedDeriv_fabiusReal`, which is
kept unchanged for compatibility; it matches the shape already used for
`extendedFabius` and `rvachevUp` in `FabiusFunction.GlobalBounds`. -/
theorem isGreatest_abs_iteratedDeriv_fabiusReal_all (F : BoundedFabius)
    (hF : IsFabius F) (k : ℕ) :
    IsGreatest (Set.range fun x : ℝ => |iteratedDeriv k (fabiusReal F) x|)
      (2 ^ (k + 1).choose 2) := by
  constructor
  · refine ⟨((2 : ℝ) ^ k)⁻¹, ?_⟩
    show |iteratedDeriv k (fabiusReal F) (((2 : ℝ) ^ k)⁻¹)| =
      2 ^ (k + 1).choose 2
    rw [iteratedDeriv_fabiusReal_inv_two_pow_all F hF k,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1).choose 2)]
  · rintro y ⟨x, rfl⟩
    exact abs_iteratedDeriv_fabiusReal_le F hF k x

end Fabius
