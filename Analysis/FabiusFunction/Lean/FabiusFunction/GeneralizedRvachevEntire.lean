import FabiusFunction.CanonicalIntegerPoint
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# The generalized Rvachev transform is entire

`FabiusFunction.GeneralizedRvachevProduct` builds the transform

`Φ_a(z) = ∏' h, complexSinc (π z / 2 ^ h) ^ (a h)`

of an admissible exponent sequence and proves that the factors are
`Multipliable` at every `z : ℂ`.  Its own header records what is
missing: "Nothing in this file asserts convergence that is uniform on
compact sets, nothing asserts that `Φ_a` is differentiable or
entire".  `FabiusFunction.GeneralizedCanonicalForm` repeated the gap,
and `FabiusFunction.CanonicalIntegerPoint` said of its factorization
`Φ_a(z) = (1 - z²/n²)^(m_a n) · R_n(z)` that turning it into an order
statement "would require, in addition, that `R_n` be analytic near
`±n` — not proved anywhere in the corpus".  (That sentence has since
been rewritten to point here; it is quoted as the statement of the
gap this module was written to close, not as current text.)

This module closes that gap for **every** admissible weight.  The
route is Mathlib's locally uniform product machinery, of which
`Mathlib.NumberTheory.ModularForms.DedekindEta` is the model use
for `∏' n, (1 - q^(n+1))^k`:

* `Summable.hasProdLocallyUniformlyOn_nat_one_add` turns a summable
  bound on the factor deviations, uniform over an open set, into
  local uniform convergence of `∏' i, (1 + f i x)`.  This is the
  `LocallyCompactSpace` form of the lemma `DedekindEta` reaches
  through `hasProdLocallyUniformlyOn_of_forall_compact`; that file
  uses the `IsCompact` sibling `Summable.hasProdUniformlyOn_nat_one_add`,
  and the locally uniform form has no other call site in Mathlib;
* `TendstoLocallyUniformlyOn.differentiableOn` (reached because
  `HasProdLocallyUniformlyOn` is by definition a
  `TendstoLocallyUniformlyOn` of the finite subproducts, each of
  which is a finite product of entire functions) makes the limit
  holomorphic on that set.

The one new estimate is the **uniformity in `z`**.  The bound proved
*inside* `Fabius.summable_natCast_mul_norm_sincFactor_sub_one`
controls the weighted deviation `a h · ‖complexSinc (π z / 2 ^ h) - 1‖`
eventually by `C · (π ‖z‖) · (a h / 2 ^ h)`; that lemma *states* only
the summability, so this module re-derives the estimate directly from
`Fabius.complexSinc_sub_one_isBigO`, with `C` replaced by `|C|`
because `Asymptotics.IsBigO.bound` yields an unsigned constant and
the majorant must be nonnegative, and with `‖z‖` replaced by the
radius `R` of a ball, which makes the bound independent of the point
-- precisely the hypothesis Mathlib wants.

Two remarks on the shape of the two bounds proved here.

* For the *scale* factors the bound holds only **eventually in `h`**:
  the corpus's linear estimate for `complexSinc w - 1` comes from
  `complexSinc_sub_one_isBigO`, valid on some neighbourhood of `0`,
  and the arguments `π z / 2 ^ h` enter that neighbourhood uniformly
  over the ball only once `2 ^ h` is large enough.  That is exactly
  the `∀ᶠ n in atTop` hypothesis of the Mathlib lemma, so nothing is
  lost.
* For the *canonical* factors the bound holds for **every** index,
  because the deviation of the base from `1` is the exact quantity
  `‖z²/(k+1)²‖ = ‖z‖²/(k+1)²`, with no `O`-estimate and hence no
  smallness hypothesis behind it.

## What is deliberately not proved here

Nothing probabilistic: the random variable `X_a`, its convolution
reading, the smoothness dichotomy and the cumulants are all absent,
as they are from the rest of the corpus.  The local analytic orders at
both positive and negative nonzero integers are computed below, while
entirety already includes `z = 0`.  No local order at zero or *global*
order statement (genus or Hadamard factorization) is claimed here, and
the growth estimate for `Φ_a` lives downstream in
`GeneralizedExponentialType.lean`.

## Main declarations

* `Fabius.mul_div_le_of_le` — the elementary rearrangement
  `M · (x / D) ≤ y · (M / D)` used to make a deviation bound
  uniform over a ball.
* `Fabius.le_mul_exp_tsum_of_le_exp_sub_one` — the arithmetic step
  extracted from `Fabius.summable_norm_of_norm_le_exp_sub_one`: a
  quantity bounded by `exp (v n) - 1` is bounded by
  `v n · exp (∑' v)`, which is the *explicit summable majorant* the
  Mathlib product lemma needs.
* `Fabius.differentiable_generalizedSincFactor` — the `h`-th raised
  sinc factor `complexSinc (π z / 2 ^ h) ^ (a h)` is entire.
* `Fabius.exists_summable_norm_generalizedSincFactor_sub_one_le` —
  **(a) the uniform bound**: on `Metric.ball 0 R` the deviations of
  the raised sinc factors are eventually dominated by a summable
  sequence that does not depend on the point.
* `Fabius.hasProdLocallyUniformlyOn_generalizedRvachevProduct` —
  **(b) locally uniform convergence** of the defining product on every
  ball `Metric.ball 0 R`.  This is the convergence the exponents
  volume asserts alongside its canonical form.
* `Fabius.differentiableOn_generalizedRvachevProduct_ball` — its
  corollary: `Φ_a` is holomorphic on every ball `Metric.ball 0 R`.
* `Fabius.generalizedRvachevProduct_differentiable` — **(c) the
  transform is entire**, for every admissible exponent sequence.
* `Fabius.analyticAt_generalizedRvachevProduct` — the corresponding
  analyticity at each point.
* `Fabius.differentiable_canonicalComplexFactor` — the canonical
  factor `(1 - z²/(k+1)²) ^ (m_a (k+1))` is entire in `z`.
* `Fabius.differentiable_canonicalCofactorFactor` — so is the
  canonical factor with the index `m` overwritten by `1`.
* `Fabius.exists_summable_norm_canonicalComplexFactor_sub_one_le` —
  the uniform bound for the canonical factors, valid at every index.
* `Fabius.differentiableOn_canonicalCofactor_ball`,
  `Fabius.canonicalCofactor_differentiable` — **(d)** the
  complementary factor `R_n` is holomorphic on every ball, hence
  entire.  This is the ingredient `CanonicalIntegerPoint` names as
  missing.
* `Fabius.canonicalComplexFactor_eq_sub_mul`,
  `Fabius.canonicalComplexFactor_eq_add_mul` — the algebraic splits
  `(1 - z²/n²)^k = (z ∓ n)^k · (∓((z ± n)/n²))^k`, exhibiting the
  zero at `z = ±n` as a `k`-th power, the second factor being a unit
  there with value `(∓2/n)^k`.
* `Fabius.analyticOrderAt_generalizedRvachevProduct_natCast` —
  **(e) the order of vanishing**
  `analyticOrderAt Φ_a (n) = m_a n` at `n = m + 1`, the volume's
  `ord_{z=n} Φ_a = m_a(n)` at a general admissible weight.
* `Fabius.analyticOrderAt_generalizedRvachevProduct_neg_natCast`,
  `Fabius.analyticOrderAt_generalizedRvachevProduct_neg_pos` — the
  **reflected** half, `analyticOrderAt Φ_a (-n) = m_a n`, which
  completes the volume's `ord_{z=±n} Φ_a = m_a(n)`.
* `Fabius.analyticOrderAt_generalizedRvachevProduct_pos`,
  `Fabius.analyticOrderAt_generalizedRvachevProduct_neg_pos` — the
  same two statements indexed by a positive natural number `n ≥ 1`.
-/

set_option autoImplicit false

open Filter

namespace Fabius

/-! ## Two elementary rearrangements -/

/-- `M · (x / D) ≤ y · (M / D)` whenever `x ≤ y` and `M / D ≥ 0`.

Both sides are `M · x / D` and `M · y / D`; the shape on the right is
the one in which a deviation bound becomes independent of the point
of a ball, with `y` the squared radius. -/
theorem mul_div_le_of_le {M D x y : ℝ} (hMD : 0 ≤ M / D)
    (hxy : x ≤ y) : M * (x / D) ≤ y * (M / D) := by
  calc M * (x / D) = M / D * x := by ring
    _ ≤ M / D * y := mul_le_mul_of_nonneg_left hxy hMD
    _ = y * (M / D) := by ring

/-- **An explicit summable majorant.**  If `v` is summable and
nonnegative and `t ≤ exp (v n) - 1`, then `t ≤ v n · exp (∑' v)`.

This is the arithmetic core of the corpus's comparison test
`Fabius.summable_norm_of_norm_le_exp_sub_one`, isolated because
Mathlib's locally uniform product lemma wants the majorant itself,
not merely the summability it implies.  The two steps are
`Fabius.exp_sub_one_le_mul_exp` and the fact that a nonnegative
summable sequence is bounded termwise by its own sum. -/
theorem le_mul_exp_tsum_of_le_exp_sub_one {v : ℕ → ℝ}
    (hv : Summable v) (h0 : ∀ n, 0 ≤ v n) {n : ℕ} {t : ℝ}
    (ht : t ≤ Real.exp (v n) - 1) :
    t ≤ v n * Real.exp (∑' m, v m) := by
  have hle : v n ≤ ∑' m, v m := hv.le_tsum n fun m _ => h0 m
  calc t ≤ Real.exp (v n) - 1 := ht
    _ ≤ v n * Real.exp (v n) := exp_sub_one_le_mul_exp (v n)
    _ ≤ v n * Real.exp (∑' m, v m) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (h0 n)

/-! ## The scale factors -/

/-- **Each raised sinc factor is entire.**  The argument
`z ↦ π z / 2 ^ h` is affine, `complexSinc` is entire
(`Fabius.complexSinc_differentiable`, the removable `sin w / w`), and
a natural power of an entire function is entire. -/
theorem differentiable_generalizedSincFactor (a : ℕ → ℕ) (h : ℕ) :
    Differentiable ℂ (fun z : ℂ =>
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h) := by
  have hinner : Differentiable ℂ
      (fun z : ℂ => (Real.pi : ℂ) * z / (2 : ℂ) ^ h) :=
    (differentiable_fun_id.const_mul _).div_const _
  exact (complexSinc_differentiable.fun_comp hinner).fun_pow (a h)

/-- **(a) The uniform bound.**  For `R > 0` there is a summable
`u : ℕ → ℝ`, independent of the point, with

`‖complexSinc (π z / 2 ^ h) ^ (a h) - 1‖ ≤ u h`

for every `z ∈ Metric.ball 0 R` and every large enough `h`.

The corpus proves the summability of the weighted deviations in
`Fabius.summable_natCast_mul_norm_sincFactor_sub_one`; its proof
passes through the estimate `‖complexSinc w - 1‖ ≤ C ‖w‖` near `0`
supplied by `Fabius.complexSinc_sub_one_isBigO`, and it is that
estimate -- not the summability statement, which is all the lemma
exports -- that is re-derived here.  It bounds the `h`-th deviation
of the *unraised* factor by `C · π ‖z‖ / 2 ^ h`
once `π z / 2 ^ h` lies in that neighbourhood.  Replacing `‖z‖` by `R` makes
that bound uniform over the ball, and the entry into the
neighbourhood is uniform too, because `π ‖z‖ / 2 ^ h ≤ π R / 2 ^ h`
and the right-hand side tends to `0`.  The power deviation bound
`Fabius.norm_one_add_pow_sub_one_le` then raises the factor to
`a h`, and `Fabius.le_mul_exp_tsum_of_le_exp_sub_one` converts the
resulting `exp (v h) - 1` into the summable majorant
`v h · exp (∑' v)`.

The quantifier order is the one Mathlib's
`Summable.hasProdLocallyUniformlyOn_nat_one_add` asks for: the bound
is eventual in `h` and uniform in `z`. -/
theorem exists_summable_norm_generalizedSincFactor_sub_one_le
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {R : ℝ} (hR : 0 < R) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ h : ℕ in atTop, ∀ z ∈ Metric.ball (0 : ℂ) R,
        ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h - 1‖
          ≤ u h := by
  obtain ⟨C, hC0⟩ := complexSinc_sub_one_isBigO.bound
  have hCabs : ∀ᶠ w : ℂ in nhds 0,
      ‖complexSinc w - 1‖ ≤ |C| * ‖w‖ := by
    filter_upwards [hC0] with w hw
    exact hw.trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg w))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hCabs
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ, ∀ h : ℕ,
      v h = |C| * (Real.pi * R) * ((a h : ℝ) / 2 ^ h) :=
    ⟨_, fun _ => rfl⟩
  have hB0 : (0 : ℝ) ≤ |C| * (Real.pi * R) :=
    mul_nonneg (abs_nonneg C)
      (mul_nonneg Real.pi_pos.le hR.le)
  have hvsum : Summable v :=
    (ha.mul_left (|C| * (Real.pi * R))).congr
      fun h => (hvdef h).symm
  have hv0 : ∀ h : ℕ, 0 ≤ v h := by
    intro h
    rw [hvdef h]
    exact mul_nonneg hB0
      (div_nonneg (Nat.cast_nonneg _) (by positivity))
  have hgeom : Tendsto (fun h : ℕ => ((2 : ℝ)⁻¹) ^ h) atTop
      (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : Tendsto (fun h : ℕ => Real.pi * R / 2 ^ h) atTop
      (nhds 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      hgeom.const_mul (Real.pi * R)
  refine ⟨fun h => v h * Real.exp (∑' m : ℕ, v m),
    hvsum.mul_right _, ?_⟩
  filter_upwards [hsmall.eventually_lt_const hε] with h hh
  intro z hz
  have hzR : ‖z‖ < R := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hnw : ‖(Real.pi : ℂ) * z / (2 : ℂ) ^ h‖
      = Real.pi * ‖z‖ / 2 ^ h := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_two]
  have hmono : Real.pi * ‖z‖ / 2 ^ h ≤ Real.pi * R / 2 ^ h := by
    have h1 : Real.pi * ‖z‖ ≤ Real.pi * R :=
      mul_le_mul_of_nonneg_left hzR.le Real.pi_pos.le
    calc Real.pi * ‖z‖ / 2 ^ h
        = Real.pi * ‖z‖ * ((2 : ℝ) ^ h)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ Real.pi * R * ((2 : ℝ) ^ h)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Real.pi * R / 2 ^ h := by rw [div_eq_mul_inv]
  have hdist : dist ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) 0 < ε := by
    rw [dist_zero_right, hnw]
    exact lt_of_le_of_lt hmono hh
  have hlin := hball hdist
  have hfac : ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1‖
      ≤ |C| * (Real.pi * R / 2 ^ h) := by
    refine hlin.trans ?_
    rw [hnw]
    exact mul_le_mul_of_nonneg_left hmono (abs_nonneg C)
  have hstep : (a h : ℝ) *
      ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1‖ ≤ v h := by
    rw [hvdef h]
    calc (a h : ℝ) *
          ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1‖
        ≤ (a h : ℝ) * (|C| * (Real.pi * R / 2 ^ h)) :=
          mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg _)
      _ = |C| * (Real.pi * R) * ((a h : ℝ) / 2 ^ h) := by ring
  have hb := norm_one_add_pow_sub_one_le
    (complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1) (a h)
  have hid : (1 : ℂ) +
      (complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1) =
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) := by ring
  rw [hid] at hb
  have hexp : Real.exp ((a h : ℝ) *
        ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1‖) - 1
      ≤ Real.exp (v h) - 1 := by
    have hle := Real.exp_le_exp.mpr hstep
    linarith
  have hfin := le_mul_exp_tsum_of_le_exp_sub_one hvsum hv0
    (hb.trans hexp)
  exact hfin

/-- **(b) Locally uniform convergence on a ball.**  For every `R > 0`
the defining product converges to `Φ_a` locally uniformly on
`Metric.ball 0 R`.

This is the hypothesis the exponents volume attaches to its canonical
form --- "with locally uniform convergence" --- and it is stated here
rather than left inside the holomorphy proof, because it is what the
volume actually asserts; holomorphy is the corollary below.

This is the Dedekind eta route of
`ModularForm.differentiableOn_tprod_one_sub_pow` -- not the
`_pow_pow` variant, whose single outer exponent `Multipliable.tprod_pow`
cannot reproduce an exponent `a h` that varies with the index -- with
the uniform bound of
`Fabius.exists_summable_norm_generalizedSincFactor_sub_one_le` in
place of the geometric one: Mathlib's
`Summable.hasProdLocallyUniformlyOn_nat_one_add` gives locally
uniform convergence of `∏' h, (1 + f h z)` on the open ball, every
partial product is a finite product of entire functions, and
`TendstoLocallyUniformlyOn.differentiableOn` transfers holomorphy to
the limit.  The final rewriting only undoes `1 + (x - 1) = x`.

Note that no nonvanishing hypothesis is needed anywhere: the
`one_add` form of the Mathlib lemma is insensitive to the zeros of
`Φ_a`, which is essential here since the ball contains them. -/
theorem hasProdLocallyUniformlyOn_generalizedRvachevProduct
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {R : ℝ} (hR : 0 < R) :
    HasProdLocallyUniformlyOn
      (fun (n : ℕ) (z : ℂ) =>
        complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ n) ^ a n)
      (generalizedRvachevProduct a) (Metric.ball (0 : ℂ) R) := by
  obtain ⟨u, hu, hbd⟩ :=
    exists_summable_norm_generalizedSincFactor_sub_one_le a ha hR
  have hcts : ∀ n : ℕ, ContinuousOn (fun z : ℂ =>
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ n) ^ a n - 1)
      (Metric.ball (0 : ℂ) R) := fun n =>
    ((differentiable_generalizedSincFactor a n).sub_const
      1).continuous.continuousOn
  have hprod := hu.hasProdLocallyUniformlyOn_nat_one_add
    (K := Metric.ball (0 : ℂ) R)
    (f := fun (n : ℕ) (z : ℂ) =>
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ n) ^ a n - 1)
    Metric.isOpen_ball hbd hcts
  have hfactor : (fun (n : ℕ) (z : ℂ) =>
      1 + (complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ n) ^ a n - 1))
      = fun (n : ℕ) (z : ℂ) =>
        complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ n) ^ a n := by
    funext n z
    ring
  have hfun : (fun z : ℂ => ∏' n : ℕ,
      (1 + (complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ n) ^ a n
        - 1))) = generalizedRvachevProduct a := by
    funext z
    show (∏' n : ℕ, (1 + (complexSinc ((Real.pi : ℂ) * z /
        (2 : ℂ) ^ n) ^ a n - 1)))
      = ∏' n : ℕ,
          complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ n) ^ a n
    exact tprod_congr fun n => by ring
  rwa [hfactor, hfun] at hprod

/-- **(b) Holomorphy on a ball**, read off from the locally uniform
convergence: every finite subproduct is a finite product of entire
functions, and `TendstoLocallyUniformlyOn.differentiableOn` --- which
`HasProdLocallyUniformlyOn.differentiableOn` unfolds to --- transfers
holomorphy to the limit. -/
theorem differentiableOn_generalizedRvachevProduct_ball
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (generalizedRvachevProduct a)
      (Metric.ball (0 : ℂ) R) := by
  refine (hasProdLocallyUniformlyOn_generalizedRvachevProduct a ha
    hR).differentiableOn ?_ Metric.isOpen_ball
  refine Filter.Eventually.of_forall fun t : Finset ℕ => ?_
  show DifferentiableOn ℂ (fun z : ℂ => ∏ n ∈ t,
    complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ n) ^ a n)
    (Metric.ball (0 : ℂ) R)
  exact DifferentiableOn.fun_finsetProd fun n _ =>
    (differentiable_generalizedSincFactor a n).differentiableOn

/-- **(c) The generalized Rvachev transform is entire.**

Every point lies in an open ball centred at the origin, and
holomorphy on an open set gives differentiability at each of its
points.  This is the statement the exponents volume needs before its
order-of-vanishing display makes sense, and the general-weight form
of `Fabius.rvachevFourierProduct_differentiable`; unlike that one it
does not pass through `existsUnique_fabius`, which exists only for
the constant weight. -/
theorem generalizedRvachevProduct_differentiable
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) :
    Differentiable ℂ (generalizedRvachevProduct a) := by
  intro z
  have hR : (0 : ℝ) < ‖z‖ + 1 := by positivity
  have hmem : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
    simp [Metric.mem_ball, dist_zero_right]
  exact (differentiableOn_generalizedRvachevProduct_ball a ha hR
    z hmem).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)

/-- The transform is analytic at every point of the plane; over `ℂ`
this is holomorphy restated. -/
theorem analyticAt_generalizedRvachevProduct
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) : AnalyticAt ℂ (generalizedRvachevProduct a) z :=
  (generalizedRvachevProduct_differentiable a ha).analyticAt z

/-! ## The canonical factors and the complementary factor -/

/-- **Each canonical factor is entire.**  The base
`1 - z²/(k+1)²` is a polynomial in `z` divided by a constant, and a
natural power of an entire function is entire. -/
theorem differentiable_canonicalComplexFactor (a : ℕ → ℕ) (k : ℕ) :
    Differentiable ℂ (fun z : ℂ => canonicalComplexFactor a z k) := by
  have hbase : Differentiable ℂ
      (fun z : ℂ => 1 - z ^ 2 / ((k + 1 : ℕ) : ℂ) ^ 2) :=
    ((differentiable_fun_id.fun_pow 2).div_const _).const_sub _
  show Differentiable ℂ (fun z : ℂ =>
    (1 - z ^ 2 / ((k + 1 : ℕ) : ℂ) ^ 2) ^
      weightedScaleMultiplicity 2 a (k + 1))
  exact hbase.fun_pow _

/-- The canonical factor with the index `m` overwritten by `1` — the
body of `Fabius.canonicalCofactor` — is entire in `z` as well: at
`k = m` it is the constant `1`, elsewhere it is the canonical
factor. -/
theorem differentiable_canonicalCofactorFactor (a : ℕ → ℕ)
    (m k : ℕ) :
    Differentiable ℂ (fun z : ℂ =>
      if k = m then (1 : ℂ) else canonicalComplexFactor a z k) := by
  by_cases hk : k = m
  · have hcst : (fun z : ℂ =>
        if k = m then (1 : ℂ) else canonicalComplexFactor a z k)
        = fun _ : ℂ => (1 : ℂ) := by
      funext z
      simp only [if_pos hk]
    rw [hcst]
    exact differentiable_const 1
  · have hcst : (fun z : ℂ =>
        if k = m then (1 : ℂ) else canonicalComplexFactor a z k)
        = fun z : ℂ => canonicalComplexFactor a z k := by
      funext z
      simp only [if_neg hk]
    rw [hcst]
    exact differentiable_canonicalComplexFactor a k

/-- **The uniform bound for the canonical factors.**  For `R > 0`
there is a summable nonnegative `u : ℕ → ℝ` with

`‖(1 - z²/(k+1)²) ^ (m_a (k+1)) - 1‖ ≤ u k`

for **every** index `k` and every `z ∈ Metric.ball 0 R`.

This is the uniform form of the corpus's
`Fabius.summable_norm_canonicalComplexFactor_sub_one`, and no
eventual quantifier is needed: the deviation of the base from `1` is
exactly `‖z‖²/(k+1)²`, which is at most `R²/(k+1)²` on the ball
without any smallness hypothesis.  The power deviation bound
`Fabius.norm_one_add_pow_sub_one_le` raises the factor to
`m_a (k+1)`, the exponent series is `R²` times the spectral zeta
series at `s = 2`
(`Fabius.summable_weightedScaleMultiplicity_div_sq`), and
`Fabius.le_mul_exp_tsum_of_le_exp_sub_one` produces the majorant. -/
theorem exists_summable_norm_canonicalComplexFactor_sub_one_le
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {R : ℝ} (hR : 0 < R) :
    ∃ u : ℕ → ℝ, Summable u ∧ (∀ k : ℕ, 0 ≤ u k) ∧
      ∀ (k : ℕ), ∀ z ∈ Metric.ball (0 : ℂ) R,
        ‖canonicalComplexFactor a z k - 1‖ ≤ u k := by
  obtain ⟨w, hwdef⟩ : ∃ w : ℕ → ℝ, ∀ k : ℕ, w k = R ^ 2 *
      (((weightedScaleMultiplicity 2 a (k + 1) : ℕ) : ℝ)
        / ((k + 1 : ℕ) : ℝ) ^ 2) := ⟨_, fun _ => rfl⟩
  have hwsum : Summable w :=
    ((summable_weightedScaleMultiplicity_div_sq a ha).mul_left
      (R ^ 2)).congr fun k => (hwdef k).symm
  have hw0 : ∀ k : ℕ, 0 ≤ w k := by
    intro k
    rw [hwdef k]
    positivity
  refine ⟨fun k => w k * Real.exp (∑' j : ℕ, w j),
    hwsum.mul_right _, ?_, ?_⟩
  · intro k
    exact mul_nonneg (hw0 k) (Real.exp_pos _).le
  intro k z hz
  have hzR : ‖z‖ < R := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hy : ‖(-(z ^ 2 / ((k + 1 : ℕ) : ℂ) ^ 2))‖
      = ‖z‖ ^ 2 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
    rw [norm_neg, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  have hb := norm_one_add_pow_sub_one_le
    (-(z ^ 2 / ((k + 1 : ℕ) : ℂ) ^ 2))
    (weightedScaleMultiplicity 2 a (k + 1))
  rw [hy] at hb
  have hid : (1 : ℂ) + -(z ^ 2 / ((k + 1 : ℕ) : ℂ) ^ 2)
      = 1 - z ^ 2 / ((k + 1 : ℕ) : ℂ) ^ 2 := by ring
  rw [hid] at hb
  have hsq : ‖z‖ ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) hzR.le 2
  have hMD : ((weightedScaleMultiplicity 2 a (k + 1) : ℕ) : ℝ)
      * (‖z‖ ^ 2 / ((k + 1 : ℕ) : ℝ) ^ 2) ≤ w k := by
    rw [hwdef k]
    exact mul_div_le_of_le (by positivity) hsq
  have hexp : Real.exp
        (((weightedScaleMultiplicity 2 a (k + 1) : ℕ) : ℝ)
          * (‖z‖ ^ 2 / ((k + 1 : ℕ) : ℝ) ^ 2)) - 1
      ≤ Real.exp (w k) - 1 := by
    have hle := Real.exp_le_exp.mpr hMD
    linarith
  have hfin := le_mul_exp_tsum_of_le_exp_sub_one hwsum hw0
    (hb.trans hexp)
  simpa only [canonicalComplexFactor] using hfin

/-- **(d) The complementary factor is holomorphic on a ball.**  For
every `R > 0` and every index `m`,

`R_n(z) = ∏'_{k ≠ m} (1 - z²/(k+1)²) ^ (m_a (k+1))`

is holomorphic on `Metric.ball 0 R`.

The proof is the one used for `Φ_a` itself, with the bound of
`Fabius.exists_summable_norm_canonicalComplexFactor_sub_one_le`: at
`k = m` the deviation is `0`, which the nonnegativity of the
majorant covers, and elsewhere it is the canonical deviation. -/
theorem differentiableOn_canonicalCofactor_ball (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (m : ℕ)
    {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (canonicalCofactor a m)
      (Metric.ball (0 : ℂ) R) := by
  obtain ⟨u, hu, hu0, hbd⟩ :=
    exists_summable_norm_canonicalComplexFactor_sub_one_le a ha hR
  have hbd' : ∀ᶠ k : ℕ in atTop, ∀ z ∈ Metric.ball (0 : ℂ) R,
      ‖(if k = m then (1 : ℂ)
        else canonicalComplexFactor a z k) - 1‖ ≤ u k := by
    refine Filter.Eventually.of_forall fun k => ?_
    intro z hz
    by_cases hk : k = m
    · rw [if_pos hk, sub_self, norm_zero]
      exact hu0 k
    · rw [if_neg hk]
      exact hbd k z hz
  have hcts : ∀ k : ℕ, ContinuousOn (fun z : ℂ =>
      (if k = m then (1 : ℂ)
        else canonicalComplexFactor a z k) - 1)
      (Metric.ball (0 : ℂ) R) := fun k =>
    ((differentiable_canonicalCofactorFactor a m k).sub_const
      1).continuous.continuousOn
  have hprod := hu.hasProdLocallyUniformlyOn_nat_one_add
    (K := Metric.ball (0 : ℂ) R)
    (f := fun (k : ℕ) (z : ℂ) =>
      (if k = m then (1 : ℂ) else canonicalComplexFactor a z k) - 1)
    Metric.isOpen_ball hbd' hcts
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => ∏' k : ℕ,
      (1 + ((if k = m then (1 : ℂ)
        else canonicalComplexFactor a z k) - 1)))
      (Metric.ball (0 : ℂ) R) := by
    refine hprod.differentiableOn ?_ Metric.isOpen_ball
    refine Filter.Eventually.of_forall fun t : Finset ℕ => ?_
    show DifferentiableOn ℂ (fun z : ℂ => ∏ k ∈ t,
      (1 + ((if k = m then (1 : ℂ)
        else canonicalComplexFactor a z k) - 1)))
      (Metric.ball (0 : ℂ) R)
    refine DifferentiableOn.fun_finsetProd fun k _ => ?_
    exact ((differentiable_canonicalCofactorFactor a m k).sub_const
      1).differentiableOn.const_add 1
  have hfun : (fun z : ℂ => ∏' k : ℕ,
      (1 + ((if k = m then (1 : ℂ)
        else canonicalComplexFactor a z k) - 1)))
      = canonicalCofactor a m := by
    funext z
    show (∏' k : ℕ, (1 + ((if k = m then (1 : ℂ)
        else canonicalComplexFactor a z k) - 1)))
      = ∏' k : ℕ,
          if k = m then (1 : ℂ) else canonicalComplexFactor a z k
    exact tprod_congr fun k => by ring
  rw [← hfun]
  exact hdiff

/-- **(d) The complementary factor is entire.**  This is the
ingredient the header of `FabiusFunction.CanonicalIntegerPoint`
names as missing: "Turning it into an order statement would require,
in addition, that `R_n` be analytic near `±n` — not proved anywhere
in the corpus." -/
theorem canonicalCofactor_differentiable (a : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) (m : ℕ) :
    Differentiable ℂ (canonicalCofactor a m) := by
  intro z
  have hR : (0 : ℝ) < ‖z‖ + 1 := by positivity
  have hmem : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
    simp [Metric.mem_ball, dist_zero_right]
  exact (differentiableOn_canonicalCofactor_ball a ha m hR
    z hmem).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)

/-! ## The order of vanishing at a positive integer -/

/-- **The canonical factor, split at its zero `z = n`.**  Writing
`n = m + 1`,

`(1 - z²/n²) ^ k = (z - n) ^ k · (-((z + n)/n²)) ^ k`,

because `1 - z²/n² = (z - n) · (-((z + n)/n²))`.  The first factor
carries the whole vanishing at `z = n`; the second does not vanish
there, its value being `(-2/n) ^ k`. -/
theorem canonicalComplexFactor_eq_sub_mul (a : ℕ → ℕ) (m : ℕ)
    (z : ℂ) :
    canonicalComplexFactor a z m =
      (z - ((m + 1 : ℕ) : ℂ)) ^
          weightedScaleMultiplicity 2 a (m + 1) *
        (-((z + ((m + 1 : ℕ) : ℂ)) / ((m + 1 : ℕ) : ℂ) ^ 2)) ^
          weightedScaleMultiplicity 2 a (m + 1) := by
  have hn : (m + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero m
  have hN : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hN2 : ((m + 1 : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hN
  have hnum : -((z - ((m + 1 : ℕ) : ℂ)) *
      (z + ((m + 1 : ℕ) : ℂ)))
      = ((m + 1 : ℕ) : ℂ) ^ 2 - z ^ 2 := by ring
  have e2 : (z - ((m + 1 : ℕ) : ℂ)) *
      (-((z + ((m + 1 : ℕ) : ℂ)) / ((m + 1 : ℕ) : ℂ) ^ 2))
      = (((m + 1 : ℕ) : ℂ) ^ 2 - z ^ 2)
          / ((m + 1 : ℕ) : ℂ) ^ 2 := by
    rw [mul_neg, ← mul_div_assoc, ← neg_div, hnum]
  have e1 : (((m + 1 : ℕ) : ℂ) ^ 2 - z ^ 2)
        / ((m + 1 : ℕ) : ℂ) ^ 2
      = 1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2 := by
    rw [sub_div, div_self hN2]
  rw [canonicalComplexFactor, ← e1, ← e2, mul_pow]

/-- **(e) The order of vanishing at a positive integer, at a general
admissible weight.**  For `n = m + 1 ≥ 1`,

`analyticOrderAt Φ_a n = m_a n`,

the exponents volume's "In particular, `ord_{z=±n} Φ_a = m_a(n)`"
attached to `p1:eq:canonical-a`, in the half that concerns `+n`.

Three inputs meet here.  `Φ_a` is analytic at `n`, by entirety
(`Fabius.generalizedRvachevProduct_differentiable`).  The corpus's
`Fabius.generalizedRvachevProduct_eq_canonicalComplexFactor_mul`
splits `Φ_a = (1 - z²/n²)^(m_a n) · R_n`, and
`Fabius.canonicalComplexFactor_eq_sub_mul` turns the first factor
into `(z - n)^(m_a n)` times a unit.  Finally `R_n` is analytic
(`Fabius.canonicalCofactor_differentiable`, tier (d)) and nonzero at
`n` (`Fabius.canonicalCofactor_natCast_ne_zero`).  Mathlib's
`AnalyticAt.analyticOrderAt_eq_natCast` then reads off the order.

The reflected point `-n` is handled by
`Fabius.analyticOrderAt_generalizedRvachevProduct_neg_natCast`
below, which needs no evenness: the mirror factorization is the same
one-line algebra. -/
theorem analyticOrderAt_generalizedRvachevProduct_natCast
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (m : ℕ) :
    analyticOrderAt (generalizedRvachevProduct a)
        ((m + 1 : ℕ) : ℂ)
      = ((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℕ∞) := by
  have hn : (m + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero m
  have hN : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hN2 : ((m + 1 : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hN
  have hW : Differentiable ℂ (fun z : ℂ =>
      -((z + ((m + 1 : ℕ) : ℂ)) / ((m + 1 : ℕ) : ℂ) ^ 2)) :=
    ((differentiable_fun_id.add_const _).div_const _).fun_neg
  have hU : Differentiable ℂ (fun z : ℂ =>
      (-((z + ((m + 1 : ℕ) : ℂ)) / ((m + 1 : ℕ) : ℂ) ^ 2)) ^
          weightedScaleMultiplicity 2 a (m + 1) *
        canonicalCofactor a m z) :=
    (hW.fun_pow _).fun_mul (canonicalCofactor_differentiable a ha m)
  have hAn : AnalyticAt ℂ (generalizedRvachevProduct a)
      ((m + 1 : ℕ) : ℂ) :=
    analyticAt_generalizedRvachevProduct a ha _
  refine hAn.analyticOrderAt_eq_natCast.mpr ⟨fun z : ℂ =>
    (-((z + ((m + 1 : ℕ) : ℂ)) / ((m + 1 : ℕ) : ℂ) ^ 2)) ^
        weightedScaleMultiplicity 2 a (m + 1) *
      canonicalCofactor a m z, hU.analyticAt _, ?_, ?_⟩
  · show (-((((m + 1 : ℕ) : ℂ) + ((m + 1 : ℕ) : ℂ)) /
        ((m + 1 : ℕ) : ℂ) ^ 2)) ^
          weightedScaleMultiplicity 2 a (m + 1) *
        canonicalCofactor a m ((m + 1 : ℕ) : ℂ) ≠ 0
    refine mul_ne_zero (pow_ne_zero _ ?_)
      (canonicalCofactor_natCast_ne_zero a ha m)
    rw [neg_ne_zero]
    refine div_ne_zero ?_ hN2
    have htwo : ((m + 1 : ℕ) : ℂ) + ((m + 1 : ℕ) : ℂ)
        = 2 * ((m + 1 : ℕ) : ℂ) := by ring
    rw [htwo]
    exact mul_ne_zero (by norm_num) hN
  · refine Filter.Eventually.of_forall fun z => ?_
    have hmain : generalizedRvachevProduct a z =
        (z - ((m + 1 : ℕ) : ℂ)) ^
            weightedScaleMultiplicity 2 a (m + 1) *
          ((-((z + ((m + 1 : ℕ) : ℂ)) /
              ((m + 1 : ℕ) : ℂ) ^ 2)) ^
              weightedScaleMultiplicity 2 a (m + 1) *
            canonicalCofactor a m z) := by
      rw [generalizedRvachevProduct_eq_canonicalComplexFactor_mul
          a ha m,
        canonicalComplexFactor_eq_sub_mul a m z, mul_assoc]
    simpa only [smul_eq_mul] using hmain

/-- **(e), indexed by a positive natural number.**  For `n ≥ 1`,

`analyticOrderAt Φ_a n = m_a n`.

At `n = 0` the statement is false in general: `Φ_a(0) = 1`
(`Fabius.generalizedRvachevProduct_at_zero`), so the order is `0`,
whereas `m_a 0 = a 0` may be any natural number.  That is the same
exception the header of `FabiusFunction.CanonicalIntegerPoint`
records for its sign law. -/
theorem analyticOrderAt_generalizedRvachevProduct_pos
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {n : ℕ} (hn : 1 ≤ n) :
    analyticOrderAt (generalizedRvachevProduct a) ((n : ℕ) : ℂ)
      = ((weightedScaleMultiplicity 2 a n : ℕ) : ℕ∞) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  exact analyticOrderAt_generalizedRvachevProduct_natCast a ha m

/-! ## The order of vanishing at a negative integer -/

/-- **The canonical factor, split at its other zero `z = -n`.**
Writing `n = m + 1`,

`(1 - z²/n²) ^ k = (z + n) ^ k · (-((z - n)/n²)) ^ k`,

the mirror of `Fabius.canonicalComplexFactor_eq_sub_mul` and the same
one-line algebra: `-(z + n)(z - n) = n² - z²`.  The first factor
carries the whole vanishing at `z = -n`; the second is a unit there,
with value `(2/n) ^ k`. -/
theorem canonicalComplexFactor_eq_add_mul (a : ℕ → ℕ) (m : ℕ)
    (z : ℂ) :
    canonicalComplexFactor a z m =
      (z + ((m + 1 : ℕ) : ℂ)) ^
          weightedScaleMultiplicity 2 a (m + 1) *
        (-((z - ((m + 1 : ℕ) : ℂ)) / ((m + 1 : ℕ) : ℂ) ^ 2)) ^
          weightedScaleMultiplicity 2 a (m + 1) := by
  have hn : (m + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero m
  have hN : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hN2 : ((m + 1 : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hN
  have hnum : -((z + ((m + 1 : ℕ) : ℂ)) *
      (z - ((m + 1 : ℕ) : ℂ)))
      = ((m + 1 : ℕ) : ℂ) ^ 2 - z ^ 2 := by ring
  have e2 : (z + ((m + 1 : ℕ) : ℂ)) *
      (-((z - ((m + 1 : ℕ) : ℂ)) / ((m + 1 : ℕ) : ℂ) ^ 2))
      = (((m + 1 : ℕ) : ℂ) ^ 2 - z ^ 2)
          / ((m + 1 : ℕ) : ℂ) ^ 2 := by
    rw [mul_neg, ← mul_div_assoc, ← neg_div, hnum]
  have e1 : (((m + 1 : ℕ) : ℂ) ^ 2 - z ^ 2)
        / ((m + 1 : ℕ) : ℂ) ^ 2
      = 1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2 := by
    rw [sub_div, div_self hN2]
  rw [canonicalComplexFactor, ← e1, ← e2, mul_pow]

/-- **(e) The order of vanishing at a negative integer.**  For
`n = m + 1 ≥ 1`,

`analyticOrderAt Φ_a (-n) = m_a n`,

which together with
`Fabius.analyticOrderAt_generalizedRvachevProduct_natCast` is the
exponents volume's `ord_{z=±n} Φ_a = m_a(n)` in full.

Evenness of `Φ_a` (`Fabius.generalizedRvachevProduct_neg`) would
transport the statement, but transporting an `analyticOrderAt` across
a reflection is more work than proving it again: the argument is
verbatim the one at `+n`, with
`Fabius.canonicalComplexFactor_eq_add_mul` in place of
`Fabius.canonicalComplexFactor_eq_sub_mul` and
`Fabius.canonicalCofactor_neg_natCast_ne_zero` in place of
`Fabius.canonicalCofactor_natCast_ne_zero`.  Both are already in the
corpus, so no import is added. -/
theorem analyticOrderAt_generalizedRvachevProduct_neg_natCast
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (m : ℕ) :
    analyticOrderAt (generalizedRvachevProduct a)
        (-((m + 1 : ℕ) : ℂ))
      = ((weightedScaleMultiplicity 2 a (m + 1) : ℕ) : ℕ∞) := by
  have hn : (m + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero m
  have hN : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hN2 : ((m + 1 : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hN
  have hW : Differentiable ℂ (fun z : ℂ =>
      -((z - ((m + 1 : ℕ) : ℂ)) / ((m + 1 : ℕ) : ℂ) ^ 2)) :=
    ((differentiable_fun_id.sub_const _).div_const _).fun_neg
  have hU : Differentiable ℂ (fun z : ℂ =>
      (-((z - ((m + 1 : ℕ) : ℂ)) / ((m + 1 : ℕ) : ℂ) ^ 2)) ^
          weightedScaleMultiplicity 2 a (m + 1) *
        canonicalCofactor a m z) :=
    (hW.fun_pow _).fun_mul (canonicalCofactor_differentiable a ha m)
  have hAn : AnalyticAt ℂ (generalizedRvachevProduct a)
      (-((m + 1 : ℕ) : ℂ)) :=
    analyticAt_generalizedRvachevProduct a ha _
  refine hAn.analyticOrderAt_eq_natCast.mpr ⟨fun z : ℂ =>
    (-((z - ((m + 1 : ℕ) : ℂ)) / ((m + 1 : ℕ) : ℂ) ^ 2)) ^
        weightedScaleMultiplicity 2 a (m + 1) *
      canonicalCofactor a m z, hU.analyticAt _, ?_, ?_⟩
  · show (-((-((m + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)) /
        ((m + 1 : ℕ) : ℂ) ^ 2)) ^
          weightedScaleMultiplicity 2 a (m + 1) *
        canonicalCofactor a m (-((m + 1 : ℕ) : ℂ)) ≠ 0
    refine mul_ne_zero (pow_ne_zero _ ?_)
      (canonicalCofactor_neg_natCast_ne_zero a ha m)
    rw [neg_ne_zero]
    refine div_ne_zero ?_ hN2
    have htwo : -((m + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ)
        = -2 * ((m + 1 : ℕ) : ℂ) := by ring
    rw [htwo]
    exact mul_ne_zero (by norm_num) hN
  · refine Filter.Eventually.of_forall fun z => ?_
    have hmain : generalizedRvachevProduct a z =
        (z - (-((m + 1 : ℕ) : ℂ))) ^
            weightedScaleMultiplicity 2 a (m + 1) *
          ((-((z - ((m + 1 : ℕ) : ℂ)) /
              ((m + 1 : ℕ) : ℂ) ^ 2)) ^
              weightedScaleMultiplicity 2 a (m + 1) *
            canonicalCofactor a m z) := by
      rw [generalizedRvachevProduct_eq_canonicalComplexFactor_mul
          a ha m,
        canonicalComplexFactor_eq_add_mul a m z, mul_assoc,
        sub_neg_eq_add]
    simpa only [smul_eq_mul] using hmain

/-- **(e) at a negative integer, indexed by `n ≥ 1`.**  The reflection
of `Fabius.analyticOrderAt_generalizedRvachevProduct_pos`; `n = 0` is
excluded for the same reason. -/
theorem analyticOrderAt_generalizedRvachevProduct_neg_pos
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    {n : ℕ} (hn : 1 ≤ n) :
    analyticOrderAt (generalizedRvachevProduct a) (-((n : ℕ) : ℂ))
      = ((weightedScaleMultiplicity 2 a n : ℕ) : ℕ∞) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  exact analyticOrderAt_generalizedRvachevProduct_neg_natCast a ha m

end Fabius
