import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Cauchy transforms of finite real measures

This module packages the literature's orientation

`C_μ(z) = ∫ (z-x)⁻¹ dμ(x)`

of Mathlib's `resolventTransform`, whose kernel has the opposite sign.  The
basic apply, affine-naturality, derivative, and holomorphy statements are
proved for an arbitrary finite real measure.

The main reusable result consumes a uniform affine fixed-point law

`μ = ((Unif[0,1]) × μ).map (fun (u,x) => c + au + bx)`

and gives its Cauchy-transform differential equation on the complement of
any invariant carrier `K`:

`C_μ'(z) = (ab)⁻¹ (C_μ((z-c)/b) - C_μ((z-c-a)/b))`.

Only finiteness, support in `K`, invariance of `K`, nonzero scales, and the
displayed equality of measures are used.  In particular, no probability
normalization, density, compactness, measurability of `K`, or moment
hypothesis is required.

## Main results

* `measureCauchyTransform_apply` gives the oriented kernel integral.
* `measureCauchyTransform_map_affine` is naturality under a nondegenerate
  affine pushforward.
* `measureCauchyPower` and `measureCauchyPower_map_affine` package every
  unnormalized resolvent power and its affine naturality.
* `hasDerivAt_measureCauchyTransform` and
  `analyticOn_measureCauchyTransform` give the ordinary calculus off support.
* `hasDerivAt_measureCauchyTransform_of_uniformAffineFixedPoint` turns a
  uniform affine fixed-point law into its exact transform DDE.
* `measureCauchyPower_succ_of_uniformAffineFixedPoint` gives the full
  adjacent-order power hierarchy under the same hypotheses.
-/

set_option autoImplicit false

open MeasureTheory Set spectrum Complex
open scoped unitInterval

namespace Fabius

/-- The natural domain of the Cauchy transform of a real measure: the
complement of its complexified topological support. -/
def measureCauchyDomain (μ : Measure ℝ) : Set ℂ :=
  (algebraMap ℝ ℂ '' μ.support)ᶜ

/-- The Cauchy transform in the orientation used in the probability and
special-function literature, `C_μ(z) = ∫ (z-x)⁻¹ dμ(x)`. -/
noncomputable def measureCauchyTransform (μ : Measure ℝ) : ℂ → ℂ :=
  fun z => -MeasureTheory.resolventTransform μ z

/-- The `n`th Cauchy kernel integral of a real measure.  Index `1` is the
ordinary oriented Cauchy transform; higher indices package the adjacent-order
resolvent hierarchy without factorial normalization. -/
noncomputable def measureCauchyPower
    (μ : Measure ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (z - (x : ℂ))⁻¹ ^ n ∂μ

private theorem neg_resolvent_eq_inv_sub (z : ℂ) (x : ℝ) :
    -resolvent z x = (z - (x : ℂ))⁻¹ := by
  rw [resolvent, Ring.inverse_eq_inv]
  rw [← inv_neg]
  congr 1
  simp only [Complex.coe_algebraMap, sub_eq_add_neg, neg_add_rev, neg_neg]

private theorem resolvent_sq_eq_inv_sub_sq (z : ℂ) (x : ℝ) :
    resolvent z x ^ 2 = (z - (x : ℂ))⁻¹ ^ 2 := by
  have h := congrArg (fun w : ℂ => w ^ 2) (neg_resolvent_eq_inv_sub z x)
  simpa only [neg_sq] using h

private theorem stronglyMeasurable_inv_sub (z : ℂ) :
    StronglyMeasurable (fun x : ℝ => (z - (x : ℂ))⁻¹) := by
  have h : Measurable (-resolvent z) :=
    (MeasureTheory.measurable_resolvent
      (𝕜 := ℝ) (A := ℂ) (a := z)).neg
  have heq : -resolvent z = fun x : ℝ => (z - (x : ℂ))⁻¹ := by
    funext x
    exact neg_resolvent_eq_inv_sub z x
  rw [heq] at h
  exact h.stronglyMeasurable

/-- The oriented Cauchy transform is the integral of `(z-x)⁻¹`.  The identity
is total under Lean's convention for nonintegrable Bochner integrals. -/
theorem measureCauchyTransform_apply (μ : Measure ℝ) (z : ℂ) :
    measureCauchyTransform μ z = ∫ x : ℝ, (z - (x : ℂ))⁻¹ ∂μ := by
  rw [measureCauchyTransform, MeasureTheory.resolventTransform_apply,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  exact neg_resolvent_eq_inv_sub z x

/-- Index one of the Cauchy-power hierarchy is the oriented Cauchy
transform. -/
@[simp] theorem measureCauchyPower_one (μ : Measure ℝ) (z : ℂ) :
    measureCauchyPower μ 1 z = measureCauchyTransform μ z := by
  rw [measureCauchyPower, measureCauchyTransform_apply]
  simp only [pow_one]

/-- Affine naturality of every Cauchy-power kernel.  The theorem is total and
does not require finiteness or integrability of the measure. -/
theorem measureCauchyPower_map_affine
    (μ : Measure ℝ) {a b : ℝ} (ha : a ≠ 0) (n : ℕ) (z : ℂ) :
    measureCauchyPower
        (μ.map (fun x : ℝ => a * x + b)) n z =
      (a : ℂ)⁻¹ ^ n *
        measureCauchyPower μ n
          ((z - (b : ℂ)) / (a : ℂ)) := by
  have hsm : StronglyMeasurable
      (fun x : ℝ => (z - (x : ℂ))⁻¹ ^ n) := by
    have heq : (fun x : ℝ => (z - (x : ℂ))⁻¹ ^ n) =
        (fun x : ℝ => (z - (x : ℂ))⁻¹) ^ n := by
      funext x
      rfl
    rw [heq]
    exact (stronglyMeasurable_inv_sub z).pow n
  rw [measureCauchyPower,
    integral_map_of_stronglyMeasurable (by fun_prop) hsm,
    measureCauchyPower, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have haC : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha
  have hden :
      z - ((a * x + b : ℝ) : ℂ) =
        (a : ℂ) * (((z - (b : ℂ)) / (a : ℂ)) - (x : ℂ)) := by
    push_cast
    field_simp
    ring
  rw [hden, mul_inv, mul_pow]

/-- Naturality of the oriented Cauchy transform under a nondegenerate affine
pushforward.  This is a total integral identity and needs no finiteness or
integrability assumption on the measure. -/
theorem measureCauchyTransform_map_affine
    (μ : Measure ℝ) {a b : ℝ} (ha : a ≠ 0) (z : ℂ) :
    measureCauchyTransform
        (μ.map (fun x : ℝ => a * x + b)) z =
      (a : ℂ)⁻¹ * measureCauchyTransform μ ((z - (b : ℂ)) / (a : ℂ)) := by
  simpa only [measureCauchyPower_one, pow_one] using
    measureCauchyPower_map_affine μ ha 1 z

/-- The natural Cauchy-transform domain is open. -/
theorem isOpen_measureCauchyDomain (μ : Measure ℝ) :
    IsOpen (measureCauchyDomain μ) := by
  rw [measureCauchyDomain]
  apply isOpen_compl_iff.mpr
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp
    Measure.isClosed_support
  exact (algebraMap_isometry ℝ ℂ).isClosedEmbedding

/-- First derivative of the oriented Cauchy transform off the complexified
support. -/
theorem hasDerivAt_measureCauchyTransform
    (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ}
    (hz : z ∈ measureCauchyDomain μ) :
    HasDerivAt (measureCauchyTransform μ)
      (-(∫ x : ℝ, (z - (x : ℂ))⁻¹ ^ 2 ∂μ)) z := by
  have h := HasDerivAt.neg (𝕜 := ℂ) (F := ℂ)
    (MeasureTheory.hasDerivAt_resolventTransform
      (𝕜 := ℝ) (A := ℂ) z hz)
  have hsq :
      (∫ x : ℝ, resolvent z x ^ 2 ∂μ) =
        ∫ x : ℝ, (z - (x : ℂ))⁻¹ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    exact resolvent_sq_eq_inv_sub_sq z x
  rw [hsq] at h
  simpa only [measureCauchyTransform] using! h

/-- The oriented Cauchy transform is holomorphic on the complement of the
complexified support of every finite real measure. -/
theorem analyticOn_measureCauchyTransform
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    AnalyticOn ℂ (measureCauchyTransform μ) (measureCauchyDomain μ) := by
  rw [Complex.analyticOn_iff_differentiableOn
    (isOpen_measureCauchyDomain μ)]
  intro z hz
  exact (hasDerivAt_measureCauchyTransform μ hz).differentiableAt
    |>.differentiableWithinAt

private theorem integrable_inv_sub_pow
    (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ}
    (hz : z ∈ measureCauchyDomain μ) (n : ℕ) :
    Integrable (fun x : ℝ => (z - (x : ℂ))⁻¹ ^ n) μ := by
  induction n with
  | zero => simpa only [pow_zero] using (integrable_const (1 : ℂ))
  | succ n ih =>
      have hbound : ∀ᵐ x : ℝ ∂μ,
          ‖(z - (x : ℂ))⁻¹‖ ≤
            (Metric.infDist z (algebraMap ℝ ℂ '' μ.support))⁻¹ := by
        filter_upwards [Measure.support_mem_ae] with x hx
        calc
          ‖(z - (x : ℂ))⁻¹‖ = ‖-resolvent z x‖ := by
            rw [neg_resolvent_eq_inv_sub]
          _ = ‖resolvent z x‖ := norm_neg _
          _ ≤ (Metric.infDist z
              (algebraMap ℝ ℂ '' μ.support))⁻¹ :=
            MeasureTheory.norm_resolvent_le_inv_infDist_support hz hx
      simpa only [pow_succ] using ih.mul_bdd
        (stronglyMeasurable_inv_sub z).aestronglyMeasurable hbound

private theorem integral_inv_sub_affine_pow
    (μ : Measure ℝ) {q c : ℝ} (hq : q ≠ 0) (n : ℕ) (z : ℂ) :
    (∫ x : ℝ, (z - ((c + q * x : ℝ) : ℂ))⁻¹ ^ n ∂μ) =
      (q : ℂ)⁻¹ ^ n *
        measureCauchyPower μ n ((z - (c : ℂ)) / (q : ℂ)) := by
  rw [measureCauchyPower, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hqC : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq
  have hden :
      z - ((c + q * x : ℝ) : ℂ) =
        (q : ℂ) * (((z - (c : ℂ)) / (q : ℂ)) - (x : ℂ)) := by
    push_cast
    field_simp
    ring
  rw [hden, mul_inv, mul_pow]

private theorem integrable_inv_sub_affine_pow
    (μ : Measure ℝ) [IsFiniteMeasure μ] {q c : ℝ} (hq : q ≠ 0)
    {z : ℂ} (n : ℕ)
    (hz : (z - (c : ℂ)) / (q : ℂ) ∈ measureCauchyDomain μ) :
    Integrable
      (fun x : ℝ => (z - ((c + q * x : ℝ) : ℂ))⁻¹ ^ n) μ := by
  have hbase :=
    (integrable_inv_sub_pow μ hz n).const_mul ((q : ℂ)⁻¹ ^ n)
  apply hbase.congr
  filter_upwards with x
  have hqC : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq
  have hden :
      z - ((c + q * x : ℝ) : ℂ) =
        (q : ℂ) * (((z - (c : ℂ)) / (q : ℂ)) - (x : ℂ)) := by
    push_cast
    field_simp
    ring
  rw [hden, mul_inv, mul_pow]

private theorem integral_unitInterval_inv_sub_affine_pow_succ
    {a c : ℝ} (ha : a ≠ 0) {z : ℂ}
    (hne : ∀ u ∈ Icc (0 : ℝ) 1,
      z - ((a * u + c : ℝ) : ℂ) ≠ 0)
    (n : ℕ) (hn : n ≠ 0) :
    (∫ u : Set.Icc (0 : ℝ) 1,
        (z - ((a * (u : ℝ) + c : ℝ) : ℂ))⁻¹ ^ (n + 1)
          ∂(volume : Measure (Set.Icc (0 : ℝ) 1))) =
      (((n : ℂ) * (a : ℂ))⁻¹) *
        ((z - ((a + c : ℝ) : ℂ))⁻¹ ^ n -
          (z - (c : ℂ))⁻¹ ^ n) := by
  let f : ℝ → ℂ := fun u =>
    (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ n
  let f' : ℝ → ℂ := fun u =>
    (n : ℂ) * (a : ℂ) *
      (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ (n + 1)
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt f (f' u) u := by
    intro u hu
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hlin : HasDerivAt (fun t : ℝ => a * t + c) a u := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id u).const_mul a).add_const c
    have houter : HasDerivAt (fun w : ℂ => (z - w)⁻¹)
        ((z - ((a * u + c : ℝ) : ℂ)) ^ 2)⁻¹
        ((a * u + c : ℝ) : ℂ) := by
      have hsub := (hasDerivAt_const ((a * u + c : ℝ) : ℂ) z).sub
        (hasDerivAt_id ((a * u + c : ℝ) : ℂ))
      have hinv := (hasDerivAt_inv (hne u hu)).comp
        ((a * u + c : ℝ) : ℂ) hsub
      simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub,
        neg_mul, mul_neg, neg_neg, mul_one] using hinv
    have hbase := houter.comp_ofReal.scomp u hlin
    change HasDerivAt
      (fun t : ℝ => (z - ((a * t + c : ℝ) : ℂ))⁻¹)
      (a • ((z - ((a * u + c : ℝ) : ℂ)) ^ 2)⁻¹) u at hbase
    have hpow := hbase.pow n
    change HasDerivAt
      (fun t : ℝ => (z - ((a * t + c : ℝ) : ℂ))⁻¹ ^ n)
      ((n : ℂ) * (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ (n - 1) *
        ((a : ℂ) * ((z - ((a * u + c : ℝ) : ℂ)) ^ 2)⁻¹)) u
      at hpow
    apply hpow.congr_deriv
    have hexp : n - 1 + 2 = n + 1 := by omega
    simp only [f']
    rw [← inv_pow]
    have hkpow :
        (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ (n - 1) *
            (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ 2 =
          (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ (n + 1) := by
      rw [← pow_add, hexp]
    calc
      (n : ℂ) * (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ (n - 1) *
          ((a : ℂ) * (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ 2) =
        (n : ℂ) * (a : ℂ) *
          ((z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ (n - 1) *
            (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ 2) := by ring
      _ = _ := by rw [hkpow]
  have hcont : ContinuousOn f' (Icc (0 : ℝ) 1) := by
    have hden : Continuous (fun u : ℝ =>
        z - ((a * u + c : ℝ) : ℂ)) := by fun_prop
    exact (continuousOn_const.mul continuousOn_const).mul
      ((hden.continuousOn.inv₀ hne).pow (n + 1))
  have hcont' : ContinuousOn f' (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont'.intervalIntegrable
  have haC : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc
    (∫ u : Set.Icc (0 : ℝ) 1,
        (z - ((a * (u : ℝ) + c : ℝ) : ℂ))⁻¹ ^ (n + 1)
          ∂(volume : Measure (Set.Icc (0 : ℝ) 1))) =
        ∫ u in Icc (0 : ℝ) 1,
          (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ (n + 1) := by
      exact integral_subtype (G := ℂ) (s := Icc (0 : ℝ) 1)
        measurableSet_Icc
        (fun u : ℝ =>
          (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ (n + 1))
    _ = ∫ u in (0 : ℝ)..1,
        (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ (n + 1) := by
      rw [integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by norm_num)]
    _ = (((n : ℂ) * (a : ℂ))⁻¹) *
        ∫ u in (0 : ℝ)..1,
          (n : ℂ) * (a : ℂ) *
            (z - ((a * u + c : ℝ) : ℂ))⁻¹ ^ (n + 1) := by
      rw [intervalIntegral.integral_const_mul]
      field_simp
    _ = (((n : ℂ) * (a : ℂ))⁻¹) * (f 1 - f 0) := by
      rw [hftc]
    _ = (((n : ℂ) * (a : ℂ))⁻¹) *
        ((z - ((a + c : ℝ) : ℂ))⁻¹ ^ n -
          (z - (c : ℂ))⁻¹ ^ n) := by
      simp only [f, mul_one, mul_zero, zero_add]

/-- **Adjacent-order Cauchy-power recurrence for a uniform affine fixed
point.**

Under the same carrier and invariance hypotheses as the transform DDE, the
unnormalized kernels satisfy

`P_(n+1)(z) = (n*a*b^n)⁻¹
  (P_n((z-c-a)/b) - P_n((z-c)/b))`

for every positive index `n`.  This division-free-in-the-measure statement
is valid for arbitrary nonzero real affine scales, including negative ones. -/
theorem measureCauchyPower_succ_of_uniformAffineFixedPoint
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b c : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) {K : Set ℝ}
    (hsupp : μ.support ⊆ K)
    (hinv : ∀ u ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      c + a * u + b * x ∈ K)
    (hfix : μ =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod μ).map
        (fun p => c + a * (p.1 : ℝ) + b * p.2))
    (n : ℕ) (hn : n ≠ 0)
    {z : ℂ} (hz : z ∉ algebraMap ℝ ℂ '' K) :
    measureCauchyPower μ (n + 1) z =
      (((n : ℂ) * (a : ℂ) * (b : ℂ) ^ n)⁻¹) *
        (measureCauchyPower μ n
            ((z - (c : ℂ) - (a : ℂ)) / (b : ℂ)) -
          measureCauchyPower μ n
            ((z - (c : ℂ)) / (b : ℂ))) := by
  let T : Set.Icc (0 : ℝ) 1 × ℝ → ℝ := fun p =>
    c + a * (p.1 : ℝ) + b * p.2
  have hzsupport : z ∈ measureCauchyDomain μ := by
    intro hzμ
    exact hz (image_mono hsupp hzμ)
  have hbranch (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      (z - (c : ℂ) - (a : ℂ) * (u : ℂ)) / (b : ℂ) ∉
        algebraMap ℝ ℂ '' K := by
    rintro ⟨x, hx, hxEq⟩
    apply hz
    refine ⟨c + a * u + b * x, hinv u hu x hx, ?_⟩
    rw [Complex.coe_algebraMap] at hxEq ⊢
    have hbC : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb
    push_cast
    rw [hxEq]
    field_simp
    ring
  have hz0I : (z - (c : ℂ)) / (b : ℂ) ∉
      algebraMap ℝ ℂ '' K := by
    simpa using hbranch 0 ⟨le_rfl, zero_le_one⟩
  have hz1I : (z - (c : ℂ) - (a : ℂ)) / (b : ℂ) ∉
      algebraMap ℝ ℂ '' K := by
    simpa using hbranch 1 ⟨zero_le_one, le_rfl⟩
  have hz0 : (z - (c : ℂ)) / (b : ℂ) ∈ measureCauchyDomain μ := by
    intro h
    exact hz0I (image_mono hsupp h)
  have hz1 : (z - (c : ℂ) - (a : ℂ)) / (b : ℂ) ∈
      measureCauchyDomain μ := by
    intro h
    exact hz1I (image_mono hsupp h)
  let k : ℝ → ℂ := fun x => (z - (x : ℂ))⁻¹ ^ (n + 1)
  have hk : Integrable k μ := integrable_inv_sub_pow μ hzsupport (n + 1)
  have hT : Measurable T := by fun_prop
  have hkprod : Integrable (fun p => k (T p))
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod μ) := by
    have hkmap : Integrable k
        (Measure.map T
          ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod μ)) := by
      rw [← hfix]
      exact hk
    exact hkmap.comp_measurable hT
  have hsm : StronglyMeasurable
      (fun x : ℝ => (z - (x : ℂ))⁻¹ ^ (n + 1)) := by
    have heq : (fun x : ℝ => (z - (x : ℂ))⁻¹ ^ (n + 1)) =
        (fun x : ℝ => (z - (x : ℂ))⁻¹) ^ (n + 1) := by
      funext x
      rfl
    rw [heq]
    exact (stronglyMeasurable_inv_sub z).pow (n + 1)
  have hprod :
      (∫ x : ℝ, k x ∂μ) =
        ∫ y : ℝ, ∫ u : Set.Icc (0 : ℝ) 1, k (T (u, y))
          ∂(volume : Measure (Set.Icc (0 : ℝ) 1)) ∂μ := by
    calc
      (∫ x : ℝ, k x ∂μ) =
          ∫ x : ℝ, k x
            ∂Measure.map T
              ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod μ) := by
        rw [← hfix]
      _ =
          ∫ p, k (T p)
            ∂((volume : Measure (Set.Icc (0 : ℝ) 1)).prod μ) := by
        exact integral_map_of_stronglyMeasurable hT (by simpa only [k] using hsm)
      _ = _ := integral_prod_symm _ hkprod
  have hinner : ∀ᵐ y ∂μ,
      (∫ u : Set.Icc (0 : ℝ) 1, k (T (u, y))
        ∂(volume : Measure (Set.Icc (0 : ℝ) 1))) =
        (((n : ℂ) * (a : ℂ))⁻¹) *
          ((z - (((c + a) + b * y : ℝ) : ℂ))⁻¹ ^ n -
            (z - ((c + b * y : ℝ) : ℂ))⁻¹ ^ n) := by
    filter_upwards [Measure.support_mem_ae] with y hy
    have hne : ∀ u ∈ Icc (0 : ℝ) 1,
        z - ((a * u + (c + b * y : ℝ) : ℝ) : ℂ) ≠ 0 := by
      intro u hu hzero
      apply hz
      refine ⟨c + a * u + b * y, hinv u hu y (hsupp hy), ?_⟩
      rw [Complex.coe_algebraMap]
      have hzEq := (sub_eq_zero.mp hzero).symm
      push_cast at hzEq ⊢
      convert hzEq using 1
      all_goals ring
    simpa only [k, T, add_assoc, add_comm, add_left_comm] using
      (integral_unitInterval_inv_sub_affine_pow_succ
        (a := a) (c := c + b * y) ha hne n hn)
  have hg0 : Integrable
      (fun y : ℝ => (z - ((c + b * y : ℝ) : ℂ))⁻¹ ^ n) μ :=
    integrable_inv_sub_affine_pow μ hb n hz0
  have hg1 : Integrable
      (fun y : ℝ =>
        (z - (((c + a) + b * y : ℝ) : ℂ))⁻¹ ^ n) μ := by
    simpa only [ofReal_add, sub_add_eq_sub_sub] using
      (integrable_inv_sub_affine_pow μ (c := c + a) hb n
        (by simpa only [ofReal_add, sub_add_eq_sub_sub] using hz1))
  have hI0 :
      (∫ y : ℝ, (z - ((c + b * y : ℝ) : ℂ))⁻¹ ^ n ∂μ) =
        (b : ℂ)⁻¹ ^ n * measureCauchyPower μ n
          ((z - (c : ℂ)) / (b : ℂ)) :=
    integral_inv_sub_affine_pow μ hb n z
  have hI1 :
      (∫ y : ℝ,
        (z - (((c + a) + b * y : ℝ) : ℂ))⁻¹ ^ n ∂μ) =
        (b : ℂ)⁻¹ ^ n * measureCauchyPower μ n
          ((z - (c : ℂ) - (a : ℂ)) / (b : ℂ)) := by
    simpa only [ofReal_add, sub_add_eq_sub_sub] using
      (integral_inv_sub_affine_pow μ (c := c + a) hb n z)
  rw [measureCauchyPower]
  change (∫ x : ℝ, k x ∂μ) = _
  rw [hprod, integral_congr_ae hinner, integral_const_mul,
    integral_sub hg1 hg0, hI1, hI0]
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have haC : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha
  have hbC : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb
  field_simp
  have hbunit : (1 / (b : ℂ)) ^ n * (b : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    field_simp
    simp
  calc
    _ = ((1 / (b : ℂ)) ^ n * (b : ℂ) ^ n) *
        (measureCauchyPower μ n
            ((z - (c : ℂ) - (a : ℂ)) / (b : ℂ)) -
          measureCauchyPower μ n
            ((z - (c : ℂ)) / (b : ℂ))) := by ring
    _ = _ := by rw [hbunit, one_mul]

/-- **Cauchy-transform DDE of a uniform affine fixed-point law.**

Let a finite real measure be carried by `K` and satisfy

`μ = ((Unif[0,1]) × μ).map (fun (u,x) => c + a*u + b*x)`.

If this affine map preserves `K`, then off the complexification of `K` its
oriented Cauchy transform satisfies

`C_μ'(z) = (a*b)⁻¹ (C_μ((z-c)/b) - C_μ((z-c-a)/b))`.

The carrier is not required to be closed, measurable, compact, or nonempty,
and no probability normalization is needed. -/
theorem hasDerivAt_measureCauchyTransform_of_uniformAffineFixedPoint
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b c : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) {K : Set ℝ}
    (hsupp : μ.support ⊆ K)
    (hinv : ∀ u ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      c + a * u + b * x ∈ K)
    (hfix : μ =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod μ).map
        (fun p => c + a * (p.1 : ℝ) + b * p.2))
    {z : ℂ} (hz : z ∉ algebraMap ℝ ℂ '' K) :
    HasDerivAt (measureCauchyTransform μ)
      ((((a * b : ℝ) : ℂ))⁻¹ *
        (measureCauchyTransform μ
            ((z - (c : ℂ)) / (b : ℂ)) -
          measureCauchyTransform μ
            ((z - (c : ℂ) - (a : ℂ)) / (b : ℂ)))) z := by
  have hzsupport : z ∈ measureCauchyDomain μ := by
    intro hzμ
    exact hz (image_mono hsupp hzμ)
  have hpow := measureCauchyPower_succ_of_uniformAffineFixedPoint
    μ ha hb hsupp hinv hfix 1 (by norm_num) hz
  have hvalue :
      -(∫ x : ℝ, (z - (x : ℂ))⁻¹ ^ 2 ∂μ) =
        ((((a * b : ℝ) : ℂ))⁻¹ *
          (measureCauchyTransform μ
              ((z - (c : ℂ)) / (b : ℂ)) -
            measureCauchyTransform μ
              ((z - (c : ℂ) - (a : ℂ)) / (b : ℂ)))) := by
    change -measureCauchyPower μ 2 z = _
    rw [show (2 : ℕ) = 1 + 1 by norm_num, hpow,
      measureCauchyPower_one, measureCauchyPower_one]
    push_cast
    norm_num
    ring
  exact (hasDerivAt_measureCauchyTransform μ hzsupport).congr_deriv hvalue

end Fabius
