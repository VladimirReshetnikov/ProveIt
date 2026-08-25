import FabiusFunction.FabiusSaddleTailAllOrders

/-!
# Asymptotics of the all-order central saddle radius

For every fixed polynomial degree, the logarithmic central radius grows more
slowly than the square root of the saddle phase.  These estimates control all
fixed-order Taylor polynomials uniformly on the expanding central interval.
Both the scalar limits and their eventual uniform-window consequences are
provided after composition with an arbitrary filter map tending to `atTop`.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Fabius

private lemma tendsto_const_mul_log_pow_div_id_atTop (C : ℝ) (d : ℕ) :
    Tendsto (fun b : ℝ => C * Real.log b ^ d / b) atTop (nhds 0) := by
  simpa [id_eq, div_eq_mul_inv, mul_assoc] using
    (Real.isLittleO_pow_log_id_atTop (n := d)).tendsto_div_nhds_zero.const_mul C

/-- For a fixed order `N` and a fixed exponent `d`, the `d`-th power of the
order-`N` central radius `fabiusSaddleCentralRadiusOrder N b`, that is of
`√(32 (N+1) log b)`, is `o(√b)`:
`(√b)⁻¹ * fabiusSaddleCentralRadiusOrder N b ^ d → 0` along `atTop`.  The
statement is for fixed `N` and `d`; no uniformity in either is claimed. -/
theorem tendsto_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow
    (N d : ℕ) :
    Tendsto (fun b : ℝ =>
      (Real.sqrt b)⁻¹ * fabiusSaddleCentralRadiusOrder N b ^ d)
      atTop (nhds 0) := by
  let C : ℝ := (32 * (N + 1 : ℝ)) ^ d
  have hbase : Tendsto (fun b : ℝ => C * Real.log b ^ d / b)
      atTop (nhds 0) := tendsto_const_mul_log_pow_div_id_atTop C d
  have hsqrt := hbase.sqrt
  have hsqrt0 : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
  rw [hsqrt0] at hsqrt
  apply hsqrt.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hsqrtb0 : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hx0 : 0 ≤
      (Real.sqrt b)⁻¹ * fabiusSaddleCentralRadiusOrder N b ^ d := by
    exact mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
      (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [← Real.sqrt_sq hx0]
  congr 1
  have hA := sq_fabiusSaddleCentralRadiusOrder N hb
  have hbsqrt := Real.sq_sqrt hb0.le
  rw [mul_pow, inv_pow, hbsqrt]
  rw [show (fabiusSaddleCentralRadiusOrder N b ^ d) ^ 2 =
      (fabiusSaddleCentralRadiusOrder N b ^ 2) ^ d by
        simp only [← pow_mul]
        congr 1
        omega]
  rw [hA]
  dsimp [C]
  rw [show 32 * (N + 1 : ℝ) * Real.log b =
      (32 * (N + 1 : ℝ)) * Real.log b by ring]
  simp only [mul_pow, div_eq_mul_inv]
  ac_rfl

/-- The order-`N` central radius is `o(√b)`:
`fabiusSaddleCentralRadiusOrder N b / √b → 0` along `atTop`.  This is the
case `d = 1` of the previous theorem, and it is the form used in
`FabiusSaddleMassAllOrders`. -/
theorem tendsto_fabiusSaddleCentralRadiusOrder_div_sqrt
    (N : ℕ) :
    Tendsto (fun b : ℝ =>
      fabiusSaddleCentralRadiusOrder N b / Real.sqrt b)
      atTop (nhds 0) := by
  simpa [div_eq_mul_inv, mul_comm] using
    tendsto_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow N 1

/-- Arbitrary-filter form of
`tendsto_fabiusSaddleCentralRadiusOrder_div_sqrt`: if `b` tends to infinity
along `l`, then the order-`N` central radius divided by `√b` tends to zero
along `l`. -/
theorem tendsto_fabiusSaddleCentralRadiusOrder_div_sqrt_comp
    {alpha : Type*} {l : Filter alpha} (b : alpha → ℝ)
    (hb : Tendsto b l atTop) (N : ℕ) :
    Tendsto (fun i =>
      fabiusSaddleCentralRadiusOrder N (b i) / Real.sqrt (b i))
      l (nhds 0) :=
  (tendsto_fabiusSaddleCentralRadiusOrder_div_sqrt N).comp hb

/-- Eventual form of the previous limit: for fixed `N` and `d`, the bound
`(√b)⁻¹ * fabiusSaddleCentralRadiusOrder N b ^ d ≤ 1` holds for all
sufficiently large `b`. -/
theorem eventually_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow_le_one
    (N d : ℕ) :
    ∀ᶠ b : ℝ in atTop,
      (Real.sqrt b)⁻¹ * fabiusSaddleCentralRadiusOrder N b ^ d ≤ 1 :=
  (tendsto_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow N d).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))

/-- Composition of
`tendsto_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow` with an arbitrary
`b : alpha → ℝ` tending to `atTop` along an arbitrary filter `l`.  This is
the form consumed by `FabiusSaddleMassAllOrders`, where `b` is the dyadic
Lambert phase. -/
theorem tendsto_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow_comp
    {alpha : Type*} {l : Filter alpha} (b : alpha → ℝ)
    (hb : Tendsto b l atTop) (N d : ℕ) :
    Tendsto (fun i =>
      (Real.sqrt (b i))⁻¹ * fabiusSaddleCentralRadiusOrder N (b i) ^ d)
      l (nhds 0) :=
  (tendsto_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow N d).comp hb

/-- Arbitrary-filter form of the eventual scalar bound: after any
`b : alpha → ℝ` tending to infinity along `l`, every fixed power of the
order-`N` central radius is eventually at most `√b`. -/
theorem eventually_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow_le_one_comp
    {alpha : Type*} {l : Filter alpha} (b : alpha → ℝ)
    (hb : Tendsto b l atTop) (N d : ℕ) :
    ∀ᶠ i in l,
      (Real.sqrt (b i))⁻¹ * fabiusSaddleCentralRadiusOrder N (b i) ^ d ≤ 1 :=
  hb.eventually
    (eventually_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow_le_one N d)

/-- Uniform version of the previous bound on the order-`N` window: for all
large `b` and every `v` in
`Icc (-fabiusSaddleCentralRadiusOrder N b) (fabiusSaddleCentralRadiusOrder N b)`
one has `(√b)⁻¹ * |v| ^ d ≤ 1`.  Both `N` and `d` are fixed; the eventual
threshold in `b` depends on them. -/
theorem eventually_inv_sqrt_mul_abs_pow_le_one_on_orderRadius
    (N d : ℕ) :
    ∀ᶠ b : ℝ in atTop, ∀ v ∈
      Icc (-fabiusSaddleCentralRadiusOrder N b)
        (fabiusSaddleCentralRadiusOrder N b),
      (Real.sqrt b)⁻¹ * |v| ^ d ≤ 1 := by
  filter_upwards
    [eventually_inv_sqrt_mul_fabiusSaddleCentralRadiusOrder_pow_le_one N d,
      eventually_ge_atTop (1 : ℝ)] with b hradius hb v hv
  have hvabs : |v| ≤ fabiusSaddleCentralRadiusOrder N b := abs_le.mpr hv
  calc
    (Real.sqrt b)⁻¹ * |v| ^ d ≤
        (Real.sqrt b)⁻¹ * fabiusSaddleCentralRadiusOrder N b ^ d := by
      gcongr
    _ ≤ 1 := hradius

/-- Arbitrary-filter form of the uniform central-window bound.  If `b` tends
to infinity along `l`, then for every fixed `N` and `d` the rescaled monomial
is eventually bounded by `1` throughout the order-`N` central interval. -/
theorem eventually_inv_sqrt_mul_abs_pow_le_one_on_orderRadius_comp
    {alpha : Type*} {l : Filter alpha} (b : alpha → ℝ)
    (hb : Tendsto b l atTop) (N d : ℕ) :
    ∀ᶠ i in l, ∀ v ∈
      Icc (-fabiusSaddleCentralRadiusOrder N (b i))
        (fabiusSaddleCentralRadiusOrder N (b i)),
      (Real.sqrt (b i))⁻¹ * |v| ^ d ≤ 1 :=
  hb.eventually
    (eventually_inv_sqrt_mul_abs_pow_le_one_on_orderRadius N d)

end Fabius
