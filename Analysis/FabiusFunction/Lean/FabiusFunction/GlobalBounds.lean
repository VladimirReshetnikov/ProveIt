import FabiusFunction.GlobalExtension
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Sharp bounds for the signed extension and all its derivatives

The signed global extension of Arias de Reyna, arXiv:1702.06487v3, equation
(1), is a locally finite sum of translates of Rvachev's function with
Thue--Morse signs.  On each interval `[2b, 2b+2]` exactly one translate
survives, so the extension is a signed copy of `up` there.  Since `up` takes
values in `[0,1]`, the extension is bounded by one in absolute value on all of
`ℝ` — a fact that the development previously never recorded, even though it is
the only missing ingredient for turning equation (3),

`F^(k)(x) = 2^C(k+1,2) F(2^k x)`,

into the sharp uniform bound `|F^(k)| ≤ 2^C(k+1,2)` for the *signed
extension* `F = extendedFabius`.  (The corresponding statement for the bounded
function `fabiusReal` is in `FabiusFunction.BoundedDerivatives`.)

Sharpness is proved as well: the value `2^C(k+1,2)` is attained at `2^(-k)`,
where `2^k x = 1` and the extension equals one.  The corresponding statements
for `up` are obtained on `[-1,1]` from equation (23) and extended to all of
`ℝ` by observing that `up` vanishes identically near every point outside its
support.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-! ## The signed extension is bounded by one -/

/--
The signed global extension takes values in `[-1, 1]`.

On `(-∞, 0]` it vanishes, and on each block `[2b, 2b+2]` it is `±up(x-2b-1)`.
-/
theorem abs_extendedFabius_le_one (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    |extendedFabius F x| ≤ 1 := by
  by_cases hx : x ≤ 0
  · rw [extendedFabius_eq_zero_of_nonpos F hF hx, abs_zero]
    norm_num
  · have hxpos : (0 : ℝ) < x := lt_of_not_ge hx
    have hx2 : (0 : ℝ) ≤ x / 2 := by positivity
    have hlo : 2 * ((⌊x / 2⌋₊ : ℕ) : ℝ) ≤ x := by
      have h := Nat.floor_le hx2
      linarith
    have hhi : x ≤ 2 * ((⌊x / 2⌋₊ : ℕ) : ℝ) + 2 := by
      have h := Nat.lt_floor_add_one (x / 2)
      linarith
    rw [extendedFabius_eq_single_translate F hF ⌊x / 2⌋₊ hlo hhi, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_rvachevUp_le_one F _

/-- The signed global extension takes values in the interval `[-1, 1]`. -/
theorem extendedFabius_mem_Icc (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    extendedFabius F x ∈ Icc (-1 : ℝ) 1 :=
  Set.mem_Icc.mpr (abs_le.mp (abs_extendedFabius_le_one F hF x))

/-! ## Sharp uniform bounds on the iterated derivatives -/

/--
Every iterated derivative of the signed extension is uniformly bounded by
`2^C(k+1,2)`, the scaling factor of equation (3).
-/
theorem abs_iteratedDeriv_extendedFabius_le (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (x : ℝ) :
    |iteratedDeriv k (extendedFabius F) x| ≤ 2 ^ (k + 1).choose 2 := by
  have h := abs_extendedFabius_le_one F hF ((2 : ℝ) ^ k * x)
  have hpow : (0 : ℝ) ≤ 2 ^ (k + 1).choose 2 := by positivity
  rw [iteratedDeriv_extendedFabius F hF k x, abs_mul, abs_of_nonneg hpow]
  nlinarith [abs_nonneg (extendedFabius F ((2 : ℝ) ^ k * x))]

/-- The uniform bound is attained at `2^(-k)`. -/
theorem iteratedDeriv_extendedFabius_inv_two_pow (F : BoundedFabius)
    (hF : IsFabius F) (k : ℕ) :
    iteratedDeriv k (extendedFabius F) (((2 : ℝ) ^ k)⁻¹) =
      2 ^ (k + 1).choose 2 := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  rw [iteratedDeriv_extendedFabius F hF k, mul_inv_cancel₀ (ne_of_gt hpos),
    extendedFabius_one F hF, mul_one]

/--
`2^C(k+1,2)` is exactly the supremum of the `k`-th derivative of the signed
extension in absolute value, and it is attained.
-/
theorem isGreatest_abs_iteratedDeriv_extendedFabius (F : BoundedFabius)
    (hF : IsFabius F) (k : ℕ) :
    IsGreatest (Set.range fun x : ℝ => |iteratedDeriv k (extendedFabius F) x|)
      (2 ^ (k + 1).choose 2) := by
  constructor
  · refine ⟨((2 : ℝ) ^ k)⁻¹, ?_⟩
    show |iteratedDeriv k (extendedFabius F) (((2 : ℝ) ^ k)⁻¹)| =
      2 ^ (k + 1).choose 2
    rw [iteratedDeriv_extendedFabius_inv_two_pow F hF k,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (k + 1).choose 2)]
  · rintro y ⟨x, rfl⟩
    exact abs_iteratedDeriv_extendedFabius_le F hF k x

/-! ## The same bounds for Rvachev's function -/

/-- Outside the support of Rvachev's function every iterated derivative
vanishes, because `up` vanishes identically near such a point. -/
theorem iteratedDeriv_rvachevUp_eq_zero_of_one_lt_abs (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) {x : ℝ} (hx : 1 < |x|) :
    iteratedDeriv n (rvachevUp F) x = 0 := by
  have hEq : rvachevUp F =ᶠ[nhds x] fun _ : ℝ => (0 : ℝ) := by
    by_cases hx0 : 0 ≤ x
    · have h : (1 : ℝ) < x := by rwa [abs_of_nonneg hx0] at hx
      filter_upwards [Ioi_mem_nhds h] with y hy
      exact rvachevUp_eq_zero_of_one_le F hF (le_of_lt hy)
    · have hneg : x < 0 := lt_of_not_ge hx0
      have h : x < -1 := by
        rw [abs_of_neg hneg] at hx
        linarith
      filter_upwards [Iio_mem_nhds h] with y hy
      exact rvachevUp_eq_zero_of_le_neg_one F hF (le_of_lt hy)
  exact (hEq.iteratedDeriv_eq n).trans iteratedDeriv_fun_const_zero

/--
Every iterated derivative of Rvachev's function vanishes outside the *open*
support, the two endpoints `±1` included: `up` is a genuine `C^∞` bump
function, flat exactly where its support closes.

This is the sharp form of `iteratedDeriv_rvachevUp_eq_zero_of_one_lt_abs`,
which stays the primitive and is deliberately left untouched: the
neighbourhood argument used there really does fail at `|x| = 1`, because `up`
is nonzero throughout `(-1, 1)` and hence not eventually zero near `±1`.  The
endpoints are reached instead by continuity of the derivative together with
`closure (Ioi 1) = Ici 1` and `closure (Iio (-1)) = Iic (-1)`.
-/
theorem iteratedDeriv_rvachevUp_eq_zero_of_one_le_abs (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) {x : ℝ} (hx : 1 ≤ |x|) :
    iteratedDeriv n (rvachevUp F) x = 0 := by
  have hcont : Continuous (iteratedDeriv n (rvachevUp F)) :=
    (rvachev_contDiff F hF).continuous_iteratedDeriv n
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hclosed : IsClosed {y : ℝ | iteratedDeriv n (rvachevUp F) y = 0} :=
    isClosed_eq hcont continuous_const
  by_cases hx0 : 0 ≤ x
  · have h1 : (1 : ℝ) ≤ x := by rwa [abs_of_nonneg hx0] at hx
    have hsub : Ioi (1 : ℝ) ⊆ {y : ℝ | iteratedDeriv n (rvachevUp F) y = 0} := by
      intro y hy
      have hy1 : (1 : ℝ) < y := mem_Ioi.mp hy
      have hy0 : (0 : ℝ) < y := by linarith
      show iteratedDeriv n (rvachevUp F) y = 0
      refine iteratedDeriv_rvachevUp_eq_zero_of_one_lt_abs F hF n ?_
      rwa [abs_of_pos hy0]
    have hmono := closure_mono hsub
    rw [closure_Ioi, hclosed.closure_eq] at hmono
    exact hmono (mem_Ici.mpr h1)
  · have hneg : x < 0 := lt_of_not_ge hx0
    have h1 : x ≤ -1 := by
      rw [abs_of_neg hneg] at hx
      linarith
    have hsub : Iio (-1 : ℝ) ⊆ {y : ℝ | iteratedDeriv n (rvachevUp F) y = 0} := by
      intro y hy
      have hy1 : y < (-1 : ℝ) := mem_Iio.mp hy
      have hy0 : y < 0 := by linarith
      show iteratedDeriv n (rvachevUp F) y = 0
      refine iteratedDeriv_rvachevUp_eq_zero_of_one_lt_abs F hF n ?_
      rw [abs_of_neg hy0]
      linarith
    have hmono := closure_mono hsub
    rw [closure_Iio, hclosed.closure_eq] at hmono
    exact hmono (mem_Iic.mpr h1)

/--
Every iterated derivative of Rvachev's function is uniformly bounded by
`2^C(n+1,2)` on all of `ℝ`.
-/
theorem abs_iteratedDeriv_rvachevUp_le (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (rvachevUp F) x| ≤ 2 ^ (n + 1).choose 2 := by
  by_cases hx : |x| ≤ 1
  · have hmem : x ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr (abs_le.mp hx)
    have h := abs_extendedFabius_le_one F hF ((2 : ℝ) ^ n * (x + 1))
    have hpow : (0 : ℝ) ≤ 2 ^ (n + 1).choose 2 := by positivity
    rw [iteratedDeriv_rvachev F hF n x hmem, abs_mul, abs_of_nonneg hpow]
    nlinarith [abs_nonneg (extendedFabius F ((2 : ℝ) ^ n * (x + 1)))]
  · rw [iteratedDeriv_rvachevUp_eq_zero_of_one_lt_abs F hF n (lt_of_not_ge hx),
      abs_zero]
    positivity

/-- The uniform bound for `up` is attained at `2^(-n) - 1`. -/
theorem iteratedDeriv_rvachevUp_inv_two_pow_sub_one (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    iteratedDeriv n (rvachevUp F) (((2 : ℝ) ^ n)⁻¹ - 1) =
      2 ^ (n + 1).choose 2 := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hinv : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hcancel : ((2 : ℝ) ^ n)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  have hle : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := by nlinarith
  have hmem : ((2 : ℝ) ^ n)⁻¹ - 1 ∈ Icc (-1 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  rw [iteratedDeriv_rvachev F hF n _ hmem,
    show ((2 : ℝ) ^ n)⁻¹ - 1 + 1 = ((2 : ℝ) ^ n)⁻¹ by ring,
    mul_inv_cancel₀ (ne_of_gt hpos), extendedFabius_one F hF, mul_one]

/-- `2^C(n+1,2)` is exactly the supremum of the `n`-th derivative of Rvachev's
function in absolute value, and it is attained. -/
theorem isGreatest_abs_iteratedDeriv_rvachevUp (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    IsGreatest (Set.range fun x : ℝ => |iteratedDeriv n (rvachevUp F) x|)
      (2 ^ (n + 1).choose 2) := by
  constructor
  · refine ⟨((2 : ℝ) ^ n)⁻¹ - 1, ?_⟩
    show |iteratedDeriv n (rvachevUp F) (((2 : ℝ) ^ n)⁻¹ - 1)| =
      2 ^ (n + 1).choose 2
    rw [iteratedDeriv_rvachevUp_inv_two_pow_sub_one F hF n,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1).choose 2)]
  · rintro y ⟨x, rfl⟩
    exact abs_iteratedDeriv_rvachevUp_le F hF n x

end Fabius
