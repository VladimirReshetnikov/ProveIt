import Lib.Base

/-!
# Fubini and convolution lemmas; idempotent kernels

General lemmas of measure and integration, and the notion of an idempotent kernel on a group.

* `New.IsBoundedMeasurable`: a strongly measurable function whose norm is bounded by a constant.
* `MeasureTheory.MeasurePreserving.integral_integral_comp`: Fubini's theorem along a
  measure-preserving map from a product; `MeasureTheory.MeasurePreserving.fubini` adds the
  integrability on the product.
* `New.integrable_integral_skew_product`, `New.integral_integral_skew_product`: Fubini's theorem
  after a substitution that preserves the measure on the space where it acts;
  `New.integral_skew_product` is the conjunction of the two.
* `New.integral_smul_integral_swap`, `New.integral_smul_integral_eq_integral_conv_smul`: the
  integral `∫ x, k x • ∫ g, α g • F (j x * g)`, for `g` in a group, in the opposite order and as a
  pairing with a convolution; `New.integral_conv` is the conjunction of the two.
* `New.IsIdempotentKernel`: a continuous integrable function `e` on a group with
  `e g⁻¹ = conj (e g)`, `e 1 ≠ 0` and `∫ e z * e ((z * x)⁻¹ * y) dz = e x⁻¹ / e 1 * e y`; in
  particular `e * e = e` (`New.IsIdempotentKernel.convolution_self`).

## Relation to the literature

The results of this file are standard. The lemmas on iterated integrals and on convolution on a
group are forms of Fubini's theorem, and `New.sq_lintegral_le` is the Cauchy–Schwarz inequality for
lower integrals, deduced from Hölder's inequality.
-/

open MeasureTheory ENNReal ComplexConjugate

namespace New

variable {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
  {μ : Measure Z} {ν : Measure W} [NormedAddCommGroup X] {F : Z → X}

/-- The function `F : Z → X` is strongly measurable, and its norm is bounded by one constant on all
of `Z`. -/
structure IsBoundedMeasurable (F : Z → X) where
  /-- `F` is strongly measurable. -/
  stronglyMeasurable : StronglyMeasurable F
  /-- The norm of `F` is bounded by a constant. -/
  bounded : ∃ C : ℝ, ∀ y : Z, ‖F y‖ ≤ C

attribute [fun_prop] IsBoundedMeasurable.stronglyMeasurable

/-- The extended nonnegative reals satisfy `1 ≠ ∞`, as a fact for instance search. -/
instance : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨one_ne_top⟩

/-- A continuous function with bounded norm on a second countable Borel space is bounded and
strongly measurable. -/
lemma IsBoundedMeasurable.of_continuous [TopologicalSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z]
    (h_bound : ∃ C : ℝ, ∀ y : Z, ‖F y‖ ≤ C) (h_cont : Continuous F := by fun_prop) :
    IsBoundedMeasurable F := ⟨h_cont.stronglyMeasurable, h_bound⟩

/-- The composition of a bounded strongly measurable function with a measurable map is bounded and
strongly measurable. -/
lemma IsBoundedMeasurable.comp (hF : IsBoundedMeasurable F) {j : W → Z} (hj : Measurable j) :
    IsBoundedMeasurable fun w : W ↦ F (j w) where
  stronglyMeasurable := hF.stronglyMeasurable.comp_measurable hj
  bounded := hF.bounded.imp fun _C hC w ↦ hC (j w)

/-- A bounded strongly measurable function lies in `L^∞` for every measure. -/
lemma IsBoundedMeasurable.memLp_top (hF : IsBoundedMeasurable F) : MemLp F ∞ μ :=
  let ⟨C, hC⟩ := hF.bounded
  memLp_top_of_bound hF.stronglyMeasurable.aestronglyMeasurable C (.of_forall hC)

/-- If `F` is strongly measurable and bounded, `c` is `ν`-integrable and `j` is measurable, then
`a ↦ c a * F (j a)` is `ν`-integrable. -/
lemma IsBoundedMeasurable.integrable_mul_comp {F : Z → ℂ} (hF : IsBoundedMeasurable F) {c : W → ℂ}
    (hc : Integrable c ν) (j : W → Z) (hj : Measurable j := by fun_prop) :
    Integrable (fun a : W ↦ c a * F (j a)) ν :=
  hc.mul_of_top_left (hF.comp hj).memLp_top

/-- Cauchy–Schwarz inequality for lower integrals of functions with values in `[0, ∞]`: if `f`,
`g` are almost everywhere measurable and `h² ≤ f g` pointwise, then `(∫ h)² ≤ ∫ f * ∫ g`. -/
lemma sq_lintegral_le {f g h : Z → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h_sq : ∀ x : Z, h x ^ 2 ≤ f x * g x) :
    lintegral μ h ^ 2 ≤ lintegral μ f * lintegral μ g := by
  -- Hölder's inequality with exponents `1/2 + 1/2 = 1`, applied to `h ≤ f ^ (1/2) * g ^ (1/2)`.
  have h_sq_iff (a b c : ℝ≥0∞) : a ^ 2 ≤ b * c ↔ a ≤ b ^ (2 : ℝ)⁻¹ * c ^ (2 : ℝ)⁻¹ := by
    simp [← mul_rpow_of_nonneg, le_rpow_inv_iff]
  rw [h_sq_iff]
  calc lintegral μ h ≤ ∫⁻ x : Z, f x ^ (2 : ℝ)⁻¹ * g x ^ (2 : ℝ)⁻¹ ∂μ :=
        lintegral_mono fun x : Z ↦ (h_sq_iff (h x) (f x) (g x)).mp (h_sq x)
    _ ≤ lintegral μ f ^ (2 : ℝ)⁻¹ * lintegral μ g ^ (2 : ℝ)⁻¹ :=
      lintegral_mul_norm_pow_le hf hg (by simp) (by simp) (by norm_num)

variable [SFinite μ] [SFinite ν]

/-- Fubini's theorem along a map `T` carrying `ν × μ` (both s-finite) to `ρ`: for a `ρ`-integrable
`f`, one has `∫∫ f (T (k, g)) dμ(g) dν(k) = ∫ f dρ`. -/
lemma _root_.MeasureTheory.MeasurePreserving.integral_integral_comp {Y : Type*}
    [MeasurableSpace Y] [NormedSpace ℝ X] {ρ : Measure Y} {T : W × Z → Y} {f : Y → X}
    (hT : MeasurePreserving T (ν.prod μ) ρ) (hf : Integrable f ρ) :
    ∫ k : W, ∫ g : Z, f (T (k, g)) ∂μ ∂ν = ∫ y : Y, f y ∂ρ :=
  calc ∫ k : W, ∫ g : Z, f (T (k, g)) ∂μ ∂ν = ∫ z : W × Z, f (T z) ∂(ν.prod μ) :=
        (integral_prod (f ∘ T) (hT.integrable_comp_of_integrable hf)).symm
    _ = ∫ y : Y, f y ∂ρ := hT.hasLaw.integral_comp hf.aestronglyMeasurable

/-- Fubini's theorem along a map `T` carrying `ν × μ` (both s-finite) to `ρ`: for a `ρ`-integrable
`f`, the function `f ∘ T` is integrable and `∫∫ f (T (k, g)) dμ(g) dν(k) = ∫ f dρ`. -/
lemma _root_.MeasureTheory.MeasurePreserving.fubini {Y : Type*} [MeasurableSpace Y]
    [NormedSpace ℝ X] {ρ : Measure Y} {T : W × Z → Y} {f : Y → X}
    (hT : MeasurePreserving T (ν.prod μ) ρ) (hf : Integrable f ρ) :
    Integrable (f ∘ T) (ν.prod μ) ∧
    ∫ k : W, ∫ g : Z, f (T (k, g)) ∂μ ∂ν = integral ρ f :=
  ⟨hT.integrable_comp_of_integrable hf, hT.integral_integral_comp hf⟩

/-- Let `μ`, `ν` be s-finite, `T` jointly measurable with each `T k` preserving `μ`, and `f`
integrable for `ν × μ`. Then `g ↦ ∫ f (k, T k g) dν(k)` is `μ`-integrable. -/
lemma integrable_integral_skew_product [NormedSpace ℝ X] {T : W → Z → Z}
    (hT_map : ∀ k : W, μ.map (T k) = μ) {f : W × Z → X} (hf : Integrable f (ν.prod μ))
    (hT : Measurable T.uncurry := by fun_prop) :
    Integrable (fun g : Z ↦ ∫ k : W, f (k, T k g) ∂ν) μ := by
  have h_preserving :
      MeasurePreserving (fun p : W × Z ↦ (p.1, T p.1 p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product hT (.of_forall hT_map)
  exact (h_preserving.integrable_comp_of_integrable hf).integral_prod_right

/-- Let `μ`, `ν` be s-finite, `T` jointly measurable with each `T k` preserving `μ`, and `f`
integrable for `ν × μ`. Then `∫∫ f (k, T k g) dν(k) dμ(g) = ∫∫ f (k, g) dμ(g) dν(k)`. -/
lemma integral_integral_skew_product [NormedSpace ℝ X] {T : W → Z → Z}
    (hT_map : ∀ k : W, μ.map (T k) = μ) {f : W × Z → X} (hf : Integrable f (ν.prod μ))
    (hT : Measurable T.uncurry := by fun_prop) :
    ∫ g : Z, ∫ k : W, f (k, T k g) ∂ν ∂μ = ∫ k : W, ∫ g : Z, f (k, g) ∂μ ∂ν := by
  -- The map `(k, g) ↦ (k, T k g)` preserves `ν.prod μ`; apply Fubini's theorem on both sides.
  have h_preserving :
      MeasurePreserving (fun p : W × Z ↦ (p.1, T p.1 p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product hT (.of_forall hT_map)
  calc ∫ g : Z, ∫ k : W, f (k, T k g) ∂ν ∂μ = ∫ k : W, ∫ g : Z, f (k, T k g) ∂μ ∂ν :=
        integral_integral_swap (h_preserving.integrable_comp_of_integrable hf).swap
    _ = ∫ p : W × Z, f p ∂(ν.prod μ) := h_preserving.integral_integral_comp hf
    _ = ∫ k : W, ∫ g : Z, f (k, g) ∂μ ∂ν := integral_prod f hf

/-- Let `μ`, `ν` be s-finite, `T` jointly measurable with each `T k` preserving `μ`, and `f`
integrable for `ν × μ`. Then `g ↦ ∫ f (k, T k g) dν(k)` is `μ`-integrable, and its integral is
`∫∫ f (k, g) dμ(g) dν(k)`. -/
lemma integral_skew_product [NormedSpace ℝ X] {T : W → Z → Z} (hT_map : ∀ k : W, μ.map (T k) = μ)
    {f : W × Z → X} (hf : Integrable f (ν.prod μ)) (hT : Measurable T.uncurry := by fun_prop) :
    Integrable (fun g : Z ↦ ∫ k : W, f (k, T k g) ∂ν) μ ∧
    ∫ g : Z, ∫ k : W, f (k, T k g) ∂ν ∂μ = ∫ k : W, ∫ g : Z, f (k, g) ∂μ ∂ν :=
  ⟨integrable_integral_skew_product hT_map hf hT, integral_integral_skew_product hT_map hf hT⟩

omit [SFinite μ] [SFinite ν] in
/-- For integrable `k` and `α`, strongly measurable bounded `F` and measurable `j : W → Z` into a
group, the function `(x, g) ↦ (k x * α g) • F (j x * g)` is integrable on the product. -/
lemma integrable_mul_smul_comp_mul [Group Z] [MeasurableMul₂ Z] [NormedSpace ℂ X] (j : W → Z)
    {k : W → ℂ} {α : Z → ℂ} (hk : Integrable k ν) (hα : Integrable α μ)
    (hF : IsBoundedMeasurable F) (hj : Measurable j := by fun_prop) :
    Integrable (fun z : W × Z ↦ (k z.1 * α z.2) • F (j z.1 * z.2)) (ν.prod μ) :=
  have h_meas : Measurable fun z : W × Z ↦ j z.1 * z.2 := by fun_prop
  (hk.mul_prod hα).smul_of_top_left (hF.comp h_meas).memLp_top

/-- For integrable `k` and `α`, strongly measurable bounded `F` and measurable `j : W → Z` into a
group, the iterated integral of `k x • α g • F (j x * g)` does not depend on the order of
integration. -/
lemma integral_smul_integral_swap [Group Z] [MeasurableMul₂ Z] [NormedSpace ℂ X]
    [CompleteSpace X] (j : W → Z) {k : W → ℂ} {α : Z → ℂ} (hk : Integrable k ν)
    (hα : Integrable α μ) (hF : IsBoundedMeasurable F) (hj : Measurable j := by fun_prop) :
    ∫ x : W, k x • ∫ g : Z, α g • F (j x * g) ∂μ ∂ν =
      ∫ g : Z, α g • ∫ x : W, k x • F (j x * g) ∂ν ∂μ := by
  have h_swap : ∫ x : W, ∫ g : Z, (k x * α g) • F (j x * g) ∂μ ∂ν =
      ∫ g : Z, ∫ x : W, (k x * α g) • F (j x * g) ∂ν ∂μ :=
    integral_integral_swap (integrable_mul_smul_comp_mul j hk hα hF hj)
  -- Move the scalar factors under the inner integrals.
  simpa [← integral_smul, smul_smul, mul_comm] using h_swap

/-- Let `μ` be left invariant on the group `Z`, `j : W → Z` measurable, `k` and `α` integrable and
`F` strongly measurable and bounded. Then `∫ k(x) ∫ α(g) F(j(x) g) dμ(g) dν(x)` equals
`∫ β(g) F(g) dμ(g)`, where `β(g) = ∫ k(x) α(j(x)⁻¹ g) dν(x)` is the convolution of `k`, carried
along `j`, and `α`. -/
lemma integral_smul_integral_eq_integral_conv_smul [Group Z] [MeasurableMul₂ Z]
    [MeasurableInv Z] [μ.IsMulLeftInvariant] [NormedSpace ℂ X] [CompleteSpace X] (j : W → Z)
    {k : W → ℂ} {α : Z → ℂ} (hk : Integrable k ν) (hα : Integrable α μ)
    (hF : IsBoundedMeasurable F) (hj : Measurable j := by fun_prop) :
    ∫ x : W, k x • ∫ g : Z, α g • F (j x * g) ∂μ ∂ν =
      ∫ g : Z, (∫ x : W, k x * α ((j x)⁻¹ * g) ∂ν) • F g ∂μ := by
  -- Fubini's theorem after the substitution `g ↦ (j x)⁻¹ * g`, which preserves `μ`.
  have h_skew :
      ∫ g : Z, ∫ x : W, (k x * α ((j x)⁻¹ * g)) • F (j x * ((j x)⁻¹ * g)) ∂ν ∂μ =
        ∫ x : W, ∫ g : Z, (k x * α g) • F (j x * g) ∂μ ∂ν :=
    integral_integral_skew_product (fun x : W ↦ map_mul_left_eq_self μ (j x)⁻¹)
      (integrable_mul_smul_comp_mul j hk hα hF hj)
  simpa [← integral_smul, ← integral_smul_const, smul_smul] using h_skew.symm

/-- For left invariant `μ`, the double integral `∫ k(x) ∫ α(g) F(j(x) g) dμ(g) dν(x)` equals both
the integral in the opposite order and the integral of `F` against the convolution of `k`, carried
along `j`, and `α`. -/
lemma integral_conv [Group Z] [MeasurableMul₂ Z] [MeasurableInv Z] [μ.IsMulLeftInvariant]
    [NormedSpace ℂ X] [CompleteSpace X] (j : W → Z) {k : W → ℂ} {α : Z → ℂ} (hk : Integrable k ν)
    (hα : Integrable α μ) (hF : IsBoundedMeasurable F) (hj : Measurable j := by fun_prop) :
    ∫ x : W, k x • ∫ g : Z, α g • F (j x * g) ∂μ ∂ν =
      ∫ g : Z, α g • ∫ x : W, k x • F (j x * g) ∂ν ∂μ ∧
    ∫ x : W, k x • ∫ g : Z, α g • F (j x * g) ∂μ ∂ν =
      ∫ g : Z, (∫ x : W, k x * α ((j x)⁻¹ * g) ∂ν) • F g ∂μ :=
  ⟨integral_smul_integral_swap j hk hα hF hj,
    integral_smul_integral_eq_integral_conv_smul j hk hα hF hj⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasureSpace G] {e : G → ℂ}

/-- The function `e` is a continuous integrable idempotent kernel on the group `G`: `e g⁻¹` is the
conjugate of `e g`, `e 1 ≠ 0`, and `∫ e z * e (x⁻¹ z⁻¹ y) dz = e x⁻¹ * e y / e 1`, the integral
being against `volume` on `G`. -/
structure IsIdempotentKernel (e : G → ℂ) where
  /-- `e` is continuous. -/
  continuous : Continuous e
  /-- `e` is integrable. -/
  integrable : Integrable e
  /-- The value of `e` at `g⁻¹` is the complex conjugate of its value at `g`. -/
  apply_inv (g : G) : e g⁻¹ = conj (e g)
  /-- `e` does not vanish at the identity. -/
  apply_one_ne_zero : e 1 ≠ 0
  /-- With `δ_x` the point mass at `x`, the convolution `e * δ_x * e` is `e x⁻¹ / e 1` times `e`. -/
  convolution_eq (x y : G) : ∫ z : G, e z * e ((z * x)⁻¹ * y) = e x⁻¹ / e 1 * e y

/-- Let `e : G → ℂ` be an idempotent kernel on the group `G` (`IsIdempotentKernel`): it is
continuous and integrable for `volume`, `e g⁻¹` is the conjugate of `e g`, `e 1 ≠ 0`, and
`∫ e z * e ((z * x)⁻¹ * y) dz = e x⁻¹ * e y / e 1` for all `x`, `y`. Then for every `y`,
`∫ e z * e (z⁻¹ * y) dz = e y`, that is `e * e = e`; this is the defining identity at `x = 1`. -/
lemma IsIdempotentKernel.convolution_self (h : IsIdempotentKernel e) (y : G) :
    ∫ z : G, e z * e (z⁻¹ * y) = e y := by
  simpa [h.apply_one_ne_zero] using h.convolution_eq 1 y

end New
