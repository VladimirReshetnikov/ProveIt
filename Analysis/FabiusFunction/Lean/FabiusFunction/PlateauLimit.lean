import FabiusFunction.PlateauConstant
import FabiusFunction.BoundedDerivatives
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The plateau at the limit: what lifts, and what does not

`PlateauConstant` proves that for `0 < p` and `r ≤ p` the `r`-th
derivative of `fabiusUniformSpline p` is the constant
`2 ^ C(r + 1, 2)` on the whole open cell of radius `2 ^ -(p+1)` around
the inverse-dyadic anchor `2 ^ -r`.  This module asks what survives in
the limit, and answers it in both directions.

**What lifts.**  The *value at the anchor* lifts exactly, and does so
already at every finite level: for `0 < p` and `r ≤ p`,

`(d/dx)^r (fabiusUniformSpline p) (2^-r)`
`  = (d/dx)^r globalFabius (2^-r) = 2 ^ C(r + 1, 2)`.

There is no error term and no limit to take; the spline side is
`PlateauConstant` evaluated at the centre of its cell, and the limit
side is `iteratedDeriv_extendedFabius_inv_two_pow` of
`FabiusFunction.GlobalBounds`, which computes the same number from
equation (3).  Since the two agree for every `p ≥ max r 1`, the
sequence of spline derivatives at the anchor is eventually constant and
therefore converges to the limit derivative.

**What does not lift: the plateau itself.**  The cells shrink, and they
shrink to nothing: they are nested (`plateauCell_subset_of_le`) and
their intersection over all levels is the single point `2 ^ -r`
(`iInter_plateauCell`).  So the set of points covered by the plateau
statement at *every* level is the anchor alone, and the naive limit
"plateau on a neighbourhood" is not merely unproved — it is **false**.
Equation (3) reads

`(d/dx)^r globalFabius x = 2 ^ C(r + 1, 2) · extendedFabius (2^r · x)`,

and on the half-line `x ≤ 2 ^ (1-r)` the signed extension takes the
value `1` at the single argument `2^r · x = 1`; everywhere else there it
is strictly below `1`, being `F` to the left of one and `1 - F` just to
the right.  Hence the limit `r`-th derivative *equals* the plateau
constant at exactly one point of that half-line
(`iteratedDeriv_globalFabius_eq_iff_dyadic`) and is strictly below it at
every other point (`iteratedDeriv_globalFabius_lt_of_ne_dyadic`).
Inside the level-`p` cell the spline therefore strictly *exceeds* the
limit at every point except the exact centre
(`iteratedDeriv_globalFabius_lt_fabiusUniformSpline_of_mem_cell`).

The half-line hypothesis `x ≤ 2 ^ (1-r)` is not a convenience: the
plateau constant is attained again at `7 · 2 ^ -r`, because the signed
extension equals `1` at `7` as well as at `1`
(`iteratedDeriv_globalFabius_eq_at_seven_dyadic`).  So "the anchor is
the unique maximiser" is true only locally, and only in the stated
range.

**Scope.**  The corpus supplies pointwise convergence of the splines
(`fabiusUniformSpline_tendsto_globalFabius_all`); the survey behind this
module turned up no convergence statement for their *derivatives*, and
none is proved here beyond the anchor, where the sequence is eventually
constant.  Nothing here says whether
`fabiusUniformSpline p` has a plateau wider than its level-`p` cell;
that question is untouched.

## Main declarations

* `plateauCell_subset_of_le` — the plateau cells are nested: the
  level-`q` cell sits inside the level-`p` cell for `p ≤ q`.
* `iInter_plateauCell` — **the cells shrink to their centre**: the
  intersection over all levels is the singleton `{a}`.
* `iteratedDeriv_fabiusUniformSpline_dyadic_center` — the plateau value
  read at the centre of the cell, for every `p ≥ r` with `0 < p`.
* `iteratedDeriv_globalFabius_dyadic`,
  `iteratedDeriv_fabiusReal_dyadic` — the same number as the `r`-th
  derivative of the limit function at `2 ^ -r`.
* `iteratedDeriv_fabiusUniformSpline_eq_globalFabius_dyadic` — **the
  lift**: spline and limit have the *same* `r`-th derivative at the
  anchor, exactly, at every admissible finite level.
* `tendsto_iteratedDeriv_fabiusUniformSpline_dyadic` — consequently the
  spline derivatives at the anchor converge to the limit derivative,
  being eventually constant.
* `extendedFabius_lt_one_of_ne_one` — on `(-∞, 2]` the signed extension
  equals one only at one.
* `iteratedDeriv_extendedFabius_lt_of_ne_dyadic`,
  `iteratedDeriv_globalFabius_lt_of_ne_dyadic` — **the obstruction**:
  strict inequality off the anchor.
* `iteratedDeriv_globalFabius_eq_iff_dyadic` — the plateau of the limit
  function is a single point.
* `iteratedDeriv_globalFabius_lt_of_mem_cell`,
  `iteratedDeriv_globalFabius_lt_fabiusUniformSpline_of_mem_cell` — the
  spline strictly overshoots the limit everywhere in its cell except at
  the centre.
* `exists_iteratedDeriv_globalFabius_lt_near_dyadic`,
  `not_locally_const_iteratedDeriv_globalFabius_dyadic`,
  `not_eventuallyEq_iteratedDeriv_globalFabius_dyadic` — **the plateau
  does not lift**: no neighbourhood of `2 ^ -r` carries it.
* `iteratedDeriv_globalFabius_eq_at_seven_dyadic` — the plateau constant
  is attained again at `7 · 2 ^ -r`, so the range hypothesis of the
  uniqueness statement cannot be dropped.
-/

set_option autoImplicit false

open scoped BigOperators Topology

namespace Fabius

/-! ### The plateau cells are nested and shrink to their centre -/

/-- A real number within `2 ^ -(p+1)` of `a` for *every* `p` is `a`. -/
private theorem eq_of_forall_abs_sub_lt_inv_two_pow {a y : ℝ}
    (h : ∀ p : ℕ, |y - a| < 1 / 2 ^ (p + 1)) : y = a := by
  by_contra hne
  have hpos : 0 < |y - a| := abs_pos.mpr (sub_ne_zero_of_ne hne)
  obtain ⟨n, hn⟩ :=
    exists_pow_lt_of_lt_one hpos (show (1 : ℝ) / 2 < 1 by norm_num)
  have hval : ((1 : ℝ) / 2) ^ n = 1 / 2 ^ n := by
    rw [div_pow, one_pow]
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hstep : (1 : ℝ) / 2 ^ (n + 1) < 1 / 2 ^ n := by
    refine one_div_lt_one_div_of_lt h2n ?_
    rw [pow_succ]
    linarith
  rw [hval] at hn
  linarith [h n]

/-- **The plateau cells are nested.**  The open cell of radius
`2 ^ -(q+1)` around `a` is contained in the one of radius `2 ^ -(p+1)`
whenever `p ≤ q`.

With `a = 2 ^ -r` these are exactly the cells on which
`iteratedDeriv_fabiusUniformSpline_dyadic` states the plateau, so
raising the level of the spline only refines the region on which the
plateau is asserted. -/
theorem plateauCell_subset_of_le (a : ℝ) {p q : ℕ} (hpq : p ≤ q) :
    Set.Ioo (a - 1 / 2 ^ (q + 1)) (a + 1 / 2 ^ (q + 1)) ⊆
      Set.Ioo (a - 1 / 2 ^ (p + 1)) (a + 1 / 2 ^ (p + 1)) := by
  have h2 : (2 : ℝ) ^ (p + 1) ≤ 2 ^ (q + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hle : (1 : ℝ) / 2 ^ (q + 1) ≤ 1 / 2 ^ (p + 1) :=
    one_div_le_one_div_of_le (by positivity) h2
  exact Set.Ioo_subset_Ioo (by linarith) (by linarith)

/-- **The plateau cells shrink to their centre.**  The intersection of
all the open cells around `a` is the singleton `{a}`.

This is the precise reason a "plateau on a fixed neighbourhood" cannot
be extracted from the level-`p` statements by intersecting them: what
survives every level is one point, not an interval.  The value at that
one point is `iteratedDeriv_fabiusUniformSpline_dyadic_center`. -/
theorem iInter_plateauCell (a : ℝ) :
    (⋂ p : ℕ, Set.Ioo (a - 1 / 2 ^ (p + 1))
      (a + 1 / 2 ^ (p + 1))) = {a} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · refine Set.mem_iInter.mpr fun p => ?_
    have hpos : (0 : ℝ) < 1 / 2 ^ (p + 1) := by positivity
    exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  · intro y hy
    refine eq_of_forall_abs_sub_lt_inv_two_pow fun p => ?_
    have h := Set.mem_Ioo.mp (Set.mem_iInter.mp hy p)
    rw [abs_lt]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ### The plateau value at the centre, and its lift -/

/-- **The plateau value at the centre of the cell.**  For `0 < p` and
`r ≤ p`,

`iteratedDeriv r (fabiusUniformSpline p) (2 ^ -r) = 2 ^ C(r + 1, 2)`.

The centre lies in the open cell at every level, so this is the one
point at which the plateau statement of `PlateauConstant` can be read
uniformly in `p`; by `iInter_plateauCell` it is also the only such
point. -/
theorem iteratedDeriv_fabiusUniformSpline_dyadic_center {p r : ℕ}
    (hp : 0 < p) (hrp : r ≤ p) :
    iteratedDeriv r (fabiusUniformSpline p) ((1 : ℝ) / 2 ^ r)
      = (2 : ℝ) ^ ((r + 1).choose 2) := by
  have hpos : (0 : ℝ) < 1 / 2 ^ (p + 1) := by positivity
  exact iteratedDeriv_fabiusUniformSpline_dyadic hp hrp _
    (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩)

/-- The `r`-th derivative of the signed global extension at the
inverse-dyadic anchor is the plateau constant:

`iteratedDeriv r globalFabius (2 ^ -r) = 2 ^ C(r + 1, 2)`.

This is `iteratedDeriv_extendedFabius_inv_two_pow` of
`FabiusFunction.GlobalBounds` at the canonical Fabius function, with
`2 ^ -r` written as `1 / 2 ^ r`. -/
theorem iteratedDeriv_globalFabius_dyadic (r : ℕ) :
    iteratedDeriv r globalFabius ((1 : ℝ) / 2 ^ r)
      = (2 : ℝ) ^ ((r + 1).choose 2) := by
  rw [globalFabius, one_div]
  exact iteratedDeriv_extendedFabius_inv_two_pow fabius fabius_spec r

/-- The same value for the bounded, CDF-style Fabius function.  The two
agree because the anchor `2 ^ -r` is at most one, where the bounded
function and the signed extension have the same germ. -/
theorem iteratedDeriv_fabiusReal_dyadic (r : ℕ) :
    iteratedDeriv r (fabiusReal fabius) ((1 : ℝ) / 2 ^ r)
      = (2 : ℝ) ^ ((r + 1).choose 2) := by
  rw [one_div]
  exact iteratedDeriv_fabiusReal_inv_two_pow_all fabius fabius_spec r

/-- **The lift of the plateau value.**  For `0 < p` and `r ≤ p` the
`r`-th derivative of the level-`p` spline at the anchor `2 ^ -r` is
*equal* to the `r`-th derivative of the limit function there.

The agreement is exact and holds at every admissible finite level: no
limit is taken, and there is no error term.  Both sides are
`2 ^ C(r + 1, 2)`. -/
theorem iteratedDeriv_fabiusUniformSpline_eq_globalFabius_dyadic
    {p r : ℕ} (hp : 0 < p) (hrp : r ≤ p) :
    iteratedDeriv r (fabiusUniformSpline p) ((1 : ℝ) / 2 ^ r)
      = iteratedDeriv r globalFabius ((1 : ℝ) / 2 ^ r) := by
  rw [iteratedDeriv_fabiusUniformSpline_dyadic_center hp hrp,
    iteratedDeriv_globalFabius_dyadic r]

/-- **Derivative convergence at the anchor.**  The `r`-th derivatives of
the centered splines at `2 ^ -r` converge to the `r`-th derivative of
the limit function there.

The convergence is trivial once the previous theorem is available: the
sequence is constant from `p = max r 1` on.  This is the only
derivative convergence proved here: no convergence of
`iteratedDeriv r (fabiusUniformSpline p)` away from the anchor is
proved, and none is used. -/
theorem tendsto_iteratedDeriv_fabiusUniformSpline_dyadic (r : ℕ) :
    Filter.Tendsto
      (fun p : ℕ =>
        iteratedDeriv r (fabiusUniformSpline p) ((1 : ℝ) / 2 ^ r))
      Filter.atTop
      (nhds (iteratedDeriv r globalFabius ((1 : ℝ) / 2 ^ r))) := by
  refine tendsto_atTop_of_eventually_const (i₀ := max r 1) ?_
  intro p hp
  have hrp : r ≤ p := (le_max_left r 1).trans hp
  have hp0 : 0 < p :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one ((le_max_right r 1).trans hp)
  exact iteratedDeriv_fabiusUniformSpline_eq_globalFabius_dyadic hp0 hrp

/-! ### The limit function has no plateau -/

/-- On the half-line `y ≤ 2` the signed extension attains the value `1`
only at `y = 1`.

To the left of one it is the bounded Fabius function, which is `< 1`
below one; on `(1, 2]` it is `1 - F(y - 1)` with `F(y - 1) > 0`.  Both
inputs are strict, which is what makes the plateau fail in the
limit. -/
theorem extendedFabius_lt_one_of_ne_one (F : BoundedFabius)
    (hF : IsFabius F) {y : ℝ} (hy : y ≤ 2) (hne : y ≠ 1) :
    extendedFabius F y < 1 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [← fabiusReal_eq_extendedFabius_of_le_one F hF hlt.le]
    exact fabius_lt_one_of_lt_one F hF hlt
  · have hmem : y - 1 ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hpos : 0 < fabiusReal F (y - 1) :=
      fabius_pos_of_pos F hF (by linarith)
    have hval := extendedFabius_one_add F hF hmem
    rw [show (1 : ℝ) + (y - 1) = y by ring] at hval
    rw [hval]
    linarith

/-- **The obstruction, for a general Fabius candidate.**  On the
half-line `x ≤ 2 ^ (1-r)` the `r`-th derivative of the signed extension
is *strictly* below the plateau constant at every point other than the
anchor `2 ^ -r`.

The proof is equation (3), `iteratedDeriv_extendedFabius`, together
with the previous lemma: the scaled argument `2 ^ r * x` lies in
`(-∞, 2]` and differs from `1`. -/
theorem iteratedDeriv_extendedFabius_lt_of_ne_dyadic
    (F : BoundedFabius) (hF : IsFabius F) (r : ℕ) {x : ℝ}
    (hx : x ≤ 2 / 2 ^ r) (hne : x ≠ 1 / 2 ^ r) :
    iteratedDeriv r (extendedFabius F) x
      < (2 : ℝ) ^ ((r + 1).choose 2) := by
  have hpow : (0 : ℝ) < 2 ^ r := by positivity
  have harg : (2 : ℝ) ^ r * x ≤ 2 := by
    rw [mul_comm]
    exact (le_div_iff₀ hpow).mp hx
  have hne' : (2 : ℝ) ^ r * x ≠ 1 := by
    intro h
    refine hne ?_
    rw [eq_div_iff hpow.ne', mul_comm]
    exact h
  have hlt := extendedFabius_lt_one_of_ne_one F hF harg hne'
  have hC : (0 : ℝ) < 2 ^ ((r + 1).choose 2) := by positivity
  have hmul := mul_lt_mul_of_pos_left hlt hC
  rw [mul_one] at hmul
  rw [iteratedDeriv_extendedFabius F hF r x]
  exact hmul

/-- **The obstruction.**  On `x ≤ 2 ^ (1-r)` the `r`-th derivative of
the limit function is strictly below the plateau constant except at the
anchor itself. -/
theorem iteratedDeriv_globalFabius_lt_of_ne_dyadic (r : ℕ) {x : ℝ}
    (hx : x ≤ 2 / 2 ^ r) (hne : x ≠ 1 / 2 ^ r) :
    iteratedDeriv r globalFabius x
      < (2 : ℝ) ^ ((r + 1).choose 2) := by
  rw [globalFabius]
  exact iteratedDeriv_extendedFabius_lt_of_ne_dyadic fabius fabius_spec
    r hx hne

/-- **The plateau of the limit function is a single point.**  On the
half-line `x ≤ 2 ^ (1-r)` the `r`-th derivative of the limit function
equals `2 ^ C(r + 1, 2)` exactly at `x = 2 ^ -r`.

Contrast `iteratedDeriv_fabiusUniformSpline_dyadic`, where the same
value is taken on a whole interval.  The range hypothesis is essential;
see `iteratedDeriv_globalFabius_eq_at_seven_dyadic`. -/
theorem iteratedDeriv_globalFabius_eq_iff_dyadic (r : ℕ) {x : ℝ}
    (hx : x ≤ 2 / 2 ^ r) :
    iteratedDeriv r globalFabius x = (2 : ℝ) ^ ((r + 1).choose 2)
      ↔ x = 1 / 2 ^ r := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hne
    exact absurd h
      (ne_of_lt (iteratedDeriv_globalFabius_lt_of_ne_dyadic r hx hne))
  · rintro rfl
    exact iteratedDeriv_globalFabius_dyadic r

/-- Every point of the level-`p` cell other than its centre already
witnesses the failure of the plateau for the limit function.  The cell
is small enough to fit inside the half-line `x ≤ 2 ^ (1-r)`, because
`r ≤ p` forces its radius `2 ^ -(p+1)` to be at most `2 ^ -r`. -/
theorem iteratedDeriv_globalFabius_lt_of_mem_cell {p r : ℕ}
    (hrp : r ≤ p) {x : ℝ}
    (hx : x ∈ Set.Ioo ((1 : ℝ) / 2 ^ r - 1 / 2 ^ (p + 1))
      ((1 : ℝ) / 2 ^ r + 1 / 2 ^ (p + 1)))
    (hne : x ≠ 1 / 2 ^ r) :
    iteratedDeriv r globalFabius x
      < (2 : ℝ) ^ ((r + 1).choose 2) := by
  refine iteratedDeriv_globalFabius_lt_of_ne_dyadic r ?_ hne
  have h2 : (2 : ℝ) ^ r ≤ 2 ^ (p + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hle : (1 : ℝ) / 2 ^ (p + 1) ≤ 1 / 2 ^ r :=
    one_div_le_one_div_of_le (by positivity) h2
  have hsplit : (2 : ℝ) / 2 ^ r = 1 / 2 ^ r + 1 / 2 ^ r := by ring
  linarith [hx.2]

/-- **The spline overshoots the limit throughout its own plateau.**  For
`0 < p` and `r ≤ p`, at every point of the open level-`p` cell around
`2 ^ -r` except the exact centre,

`(d/dx)^r globalFabius x < (d/dx)^r (fabiusUniformSpline p) x`,

the right-hand side being the constant `2 ^ C(r + 1, 2)`.  At the
centre the two are equal, by
`iteratedDeriv_fabiusUniformSpline_eq_globalFabius_dyadic`.  So the
plateau is a genuine finite-level artefact: it is flat where the limit
is not. -/
theorem iteratedDeriv_globalFabius_lt_fabiusUniformSpline_of_mem_cell
    {p r : ℕ} (hp : 0 < p) (hrp : r ≤ p) {x : ℝ}
    (hx : x ∈ Set.Ioo ((1 : ℝ) / 2 ^ r - 1 / 2 ^ (p + 1))
      ((1 : ℝ) / 2 ^ r + 1 / 2 ^ (p + 1)))
    (hne : x ≠ 1 / 2 ^ r) :
    iteratedDeriv r globalFabius x
      < iteratedDeriv r (fabiusUniformSpline p) x := by
  rw [iteratedDeriv_fabiusUniformSpline_dyadic hp hrp x hx]
  exact iteratedDeriv_globalFabius_lt_of_mem_cell hrp hx hne

/-- Arbitrarily close to the anchor, on its left, the `r`-th derivative
of the limit function is strictly below the plateau constant.  The
witness is `2 ^ -r - δ / 2`. -/
theorem exists_iteratedDeriv_globalFabius_lt_near_dyadic (r : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ x ∈ Set.Ioo ((1 : ℝ) / 2 ^ r - δ) ((1 : ℝ) / 2 ^ r + δ),
      iteratedDeriv r globalFabius x
        < (2 : ℝ) ^ ((r + 1).choose 2) := by
  have hsplit : (2 : ℝ) / 2 ^ r = 1 / 2 ^ r + 1 / 2 ^ r := by ring
  have hpos : (0 : ℝ) < 1 / 2 ^ r := by positivity
  refine ⟨1 / 2 ^ r - δ / 2,
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩, ?_⟩
  exact iteratedDeriv_globalFabius_lt_of_ne_dyadic r (by linarith)
    (by intro h; linarith)

/-- **The plateau does not lift.**  There is no `δ > 0` on whose
neighbourhood of `2 ^ -r` the `r`-th derivative of the limit function is
constant.

Together with `iteratedDeriv_fabiusUniformSpline_dyadic`, which gives
the plateau on a nondegenerate interval at every finite level, this
settles the lifting question negatively: only the value at the anchor
survives. -/
theorem not_locally_const_iteratedDeriv_globalFabius_dyadic (r : ℕ) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Ioo ((1 : ℝ) / 2 ^ r - δ)
        ((1 : ℝ) / 2 ^ r + δ),
      iteratedDeriv r globalFabius x
        = iteratedDeriv r globalFabius ((1 : ℝ) / 2 ^ r) := by
  rintro ⟨δ, hδ, h⟩
  obtain ⟨x, hx, hlt⟩ :=
    exists_iteratedDeriv_globalFabius_lt_near_dyadic r hδ
  rw [iteratedDeriv_globalFabius_dyadic r] at h
  exact absurd (h x hx) (ne_of_lt hlt)

/-- The filter form of the same statement: the `r`-th derivative of the
limit function is not eventually equal to the plateau constant near the
anchor. -/
theorem not_eventuallyEq_iteratedDeriv_globalFabius_dyadic (r : ℕ) :
    ¬ (iteratedDeriv r globalFabius =ᶠ[nhds ((1 : ℝ) / 2 ^ r)]
        fun _ : ℝ => (2 : ℝ) ^ ((r + 1).choose 2)) := by
  intro hev
  have hev' : ∀ᶠ y in nhds ((1 : ℝ) / 2 ^ r),
      iteratedDeriv r globalFabius y
        = (2 : ℝ) ^ ((r + 1).choose 2) := hev
  rw [Filter.eventually_iff] at hev'
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hev'
  rw [Real.ball_eq_Ioo] at hball
  obtain ⟨x, hx, hlt⟩ :=
    exists_iteratedDeriv_globalFabius_lt_near_dyadic r hδ
  have heq : iteratedDeriv r globalFabius x
      = (2 : ℝ) ^ ((r + 1).choose 2) := hball hx
  exact absurd heq (ne_of_lt hlt)

/-! ### The range hypothesis cannot be dropped -/

/-- **A second attainment point.**  The plateau constant is reached
again at `7 · 2 ^ -r`, which is strictly to the right of the anchor:

`(1 : ℝ) / 2 ^ r < 7 / 2 ^ r` and
`iteratedDeriv r globalFabius (7 / 2 ^ r) = 2 ^ C(r + 1, 2)`.

The reason is that the signed extension equals `1` at `7` as well as at
`1`: the block containing `7` is indexed by `b = 3`, whose binary weight
`2` is even, and `up` peaks at `7 - 2·3 - 1 = 0`.  Consequently the
hypothesis `x ≤ 2 ^ (1-r)` in
`iteratedDeriv_globalFabius_eq_iff_dyadic` cannot be removed, and the
sharp bound `abs_iteratedDeriv_extendedFabius_le` is attained at more
than one point. -/
theorem iteratedDeriv_globalFabius_eq_at_seven_dyadic (r : ℕ) :
    (1 : ℝ) / 2 ^ r < 7 / 2 ^ r ∧
      iteratedDeriv r globalFabius ((7 : ℝ) / 2 ^ r)
        = (2 : ℝ) ^ ((r + 1).choose 2) := by
  have hpow : (0 : ℝ) < 2 ^ r := by positivity
  constructor
  · have hgap : (7 : ℝ) / 2 ^ r = 1 / 2 ^ r + 6 / 2 ^ r := by ring
    have h6 : (0 : ℝ) < 6 / 2 ^ r := by positivity
    linarith
  · have hw0 : binaryWeight 0 = 0 := by
      norm_num [binaryWeight, Nat.digits_zero]
    have hw1 : binaryWeight 1 = 1 := by
      have h := binaryWeight_two_mul_add_one 0
      norm_num [hw0] at h
      exact h
    have hw3 : binaryWeight 3 = 2 := by
      have h := binaryWeight_two_mul_add_one 1
      norm_num [hw1] at h
      exact h
    have hext : extendedFabius fabius 7 = 1 := by
      have h := extendedFabius_eq_single_translate fabius fabius_spec 3
        (x := (7 : ℝ)) (by norm_num) (by norm_num)
      have harg : (7 : ℝ) - 2 * ((3 : ℕ) : ℝ) - 1 = 0 := by norm_num
      rw [harg, rvachevUp_zero fabius fabius_spec, hw3] at h
      rw [h]
      norm_num
    have hne2 : (2 : ℝ) ^ r ≠ 0 := hpow.ne'
    have hcancel : (2 : ℝ) ^ r * (7 / 2 ^ r) = 7 :=
      mul_div_cancel₀ (7 : ℝ) hne2
    rw [globalFabius, iteratedDeriv_extendedFabius fabius fabius_spec r,
      hcancel, hext, mul_one]

end Fabius
