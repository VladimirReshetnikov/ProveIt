import FabiusFunction.StieltjesInversion
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The Lebesgue-side Poisson approximate identity

`FabiusFunction.StieltjesInversion` collects the kernel
`t ↦ ε/((x-t)² + ε²)` behind `Fabius.im_rvachevCauchyTransform_eq`,
its `π⁻¹`-normalisation, and a far-field bound *against the
up-measure*.  That module's scope note says the Lebesgue-side tail
was left open, because it needs the `arctan` antiderivative rather
than the finite-measure bound.  This module supplies it.

Every integral computed here is evaluated exactly rather than
estimated; the two `ε → 0⁺` limits and the positivity guard are read
off from those exact values.  The
function `A(s) = arctan ((s - x)/ε)` is an antiderivative of the
kernel (`hasDerivAt_arctan_poisson`), and FTC-2 on the two
half-lines gives the *same* value on each side,

`∫_{Iic (x-δ)} = ∫_{Ioi (x+δ)} = π/2 - arctan (δ/ε)`,

hence the two-sided tail `π - 2·arctan (δ/ε)`.  After the `π⁻¹`
normalisation the tail is `1 - (2/π)·arctan (δ/ε)` and the
complementary mass on `(x-δ, x+δ)` is `(2/π)·arctan (δ/ε)`.

Two guards on the reading of those formulas are proved rather than
asserted.  The tail is *strictly positive* for every `ε > 0`, so
`0` is a limit and never a value; and at the calibrating choice
`δ = ε` the tail is exactly `1/2`.

The `ε → 0⁺` limits follow, and with the normalisation already
available from `StieltjesInversion` they assemble into the
approximate-identity statement `poisson_kernel_approximate_identity`:
unit total mass for every `ε > 0`, and full concentration on every
interval `(x - δ, x + δ)` with `δ > 0`.

## Scope

Stieltjes--Perron inversion is *not* proved here, and no statement
about the up-measure is made; the up-measure side lives in
`FabiusFunction.StieltjesInversion`.  This module is exactly the
Lebesgue behaviour of the kernel.

## Main declarations

* `Fabius.hasDerivAt_arctan_poisson` — **the antiderivative**:
  `s ↦ arctan ((s - x)/ε)` has the Poisson kernel as derivative.
* `Fabius.setIntegral_poisson_kernel_Ioi` — the right half-line
  integral `π/2 - arctan (δ/ε)`.
* `Fabius.setIntegral_poisson_kernel_Iic` — the left half-line
  integral, the same value.
* `Fabius.setIntegral_poisson_kernel_compl_Ioo` — the two-sided
  tail `π - 2·arctan (δ/ε)`.
* `Fabius.setIntegral_poisson_density_compl_Ioo` — **the exact
  Lebesgue tail** `1 - (2/π)·arctan (δ/ε)`.
* `Fabius.setIntegral_poisson_density_Ioo` — the near-field mass
  `(2/π)·arctan (δ/ε)`.
* `Fabius.setIntegral_poisson_density_compl_Ioo_pos` — the tail is
  strictly positive for every `ε > 0`.
* `Fabius.setIntegral_poisson_density_compl_Ioo_self` — the
  calibration `δ = ε`: the tail is exactly `1/2`.
* `Fabius.tendsto_setIntegral_poisson_density_compl_Ioo` — the tail
  tends to `0` as `ε → 0⁺`.
* `Fabius.tendsto_setIntegral_poisson_density_Ioo` — the near-field
  mass tends to `1`.
* `Fabius.poisson_kernel_approximate_identity` — **the approximate
  identity**: unit mass at every `ε > 0`, concentrating on every
  interval `(x - δ, x + δ)` with `δ > 0`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Real

namespace Fabius

/-! ### The arctangent antiderivative -/

/-- **The Poisson antiderivative**: for `ε > 0` the function
`s ↦ arctan ((s - x)/ε)` has derivative `ε/((x-t)² + ε²)` at every
real `t`. -/
theorem hasDerivAt_arctan_poisson (x : ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.arctan ((s - x) / ε))
      (ε / ((x - t) ^ 2 + ε ^ 2)) t := by
  have hε' : ε ≠ 0 := ne_of_gt hε
  have h1 : HasDerivAt (fun s : ℝ => s - x) 1 t :=
    (hasDerivAt_id' t).sub_const x
  have h2 : HasDerivAt (fun s : ℝ => (s - x) / ε) (1 / ε) t :=
    h1.div_const ε
  have h3 : HasDerivAt (fun s : ℝ => Real.arctan ((s - x) / ε))
      (1 / (1 + ((t - x) / ε) ^ 2) * (1 / ε)) t := h2.arctan
  have hts : (t - x) ^ 2 = (x - t) ^ 2 := by ring
  have hu : ((t - x) / ε) ^ 2 = (x - t) ^ 2 / ε ^ 2 := by
    rw [div_pow, hts]
  have hA : (1 : ℝ) + (x - t) ^ 2 / ε ^ 2
      = ((x - t) ^ 2 + ε ^ 2) / ε ^ 2 := by
    rw [add_div, div_self (pow_ne_zero 2 hε')]
    ring
  have hsq : ε ^ 2 = ε * ε := by ring
  have hval : 1 / (1 + ((t - x) / ε) ^ 2) * (1 / ε)
      = ε / ((x - t) ^ 2 + ε ^ 2) := by
    rw [hu, hA, one_div_div, div_mul_eq_mul_div, one_div, hsq,
      mul_assoc, mul_inv_cancel₀ hε', mul_one]
  rwa [hval] at h3

/-! ### The two half-line tails -/

private theorem tendsto_scaled_atTop (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun u : ℝ => (u - x) / ε) Filter.atTop
      Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun b => ⟨x + b * ε, ?_⟩
  intro a ha
  rw [le_div_iff₀ hε]
  linarith

private theorem tendsto_scaled_atBot (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun u : ℝ => (u - x) / ε) Filter.atBot
      Filter.atBot := by
  refine Filter.tendsto_atBot_atBot.2 fun b => ⟨x + b * ε, ?_⟩
  intro a ha
  rw [div_le_iff₀ hε]
  linarith

/-- **The right-hand tail**: for `ε > 0` the Poisson kernel
integrates over `(x + δ, ∞)` to `π/2 - arctan (δ/ε)`.  No sign
condition on `δ` is needed. -/
theorem setIntegral_poisson_kernel_Ioi (x : ℝ) {ε δ : ℝ}
    (hε : 0 < ε) :
    ∫ t in Set.Ioi (x + δ), ε / ((x - t) ^ 2 + ε ^ 2)
      = π / 2 - Real.arctan (δ / ε) := by
  have hderiv : ∀ s ∈ Set.Ici (x + δ),
      HasDerivAt (fun u : ℝ => Real.arctan ((u - x) / ε))
        (ε / ((x - s) ^ 2 + ε ^ 2)) s :=
    fun s _ => hasDerivAt_arctan_poisson x hε s
  have hint : IntegrableOn
      (fun t : ℝ => ε / ((x - t) ^ 2 + ε ^ 2))
      (Set.Ioi (x + δ)) :=
    (integrable_poisson_kernel x hε).integrableOn
  have hlim : Filter.Tendsto
      (fun u : ℝ => Real.arctan ((u - x) / ε)) Filter.atTop
      (nhds (π / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atTop.comp (tendsto_scaled_atTop x hε))
  have h : ∫ t in Set.Ioi (x + δ), ε / ((x - t) ^ 2 + ε ^ 2)
      = π / 2 - Real.arctan ((x + δ - x) / ε) :=
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have harg : (x + δ - x) / ε = δ / ε := by ring
  rw [h, harg]

/-- **The left-hand tail**: for `ε > 0` the Poisson kernel
integrates over `(-∞, x - δ]` to `π/2 - arctan (δ/ε)`, the same
value as the right-hand tail. -/
theorem setIntegral_poisson_kernel_Iic (x : ℝ) {ε δ : ℝ}
    (hε : 0 < ε) :
    ∫ t in Set.Iic (x - δ), ε / ((x - t) ^ 2 + ε ^ 2)
      = π / 2 - Real.arctan (δ / ε) := by
  have hderiv : ∀ s ∈ Set.Iic (x - δ),
      HasDerivAt (fun u : ℝ => Real.arctan ((u - x) / ε))
        (ε / ((x - s) ^ 2 + ε ^ 2)) s :=
    fun s _ => hasDerivAt_arctan_poisson x hε s
  have hint : IntegrableOn
      (fun t : ℝ => ε / ((x - t) ^ 2 + ε ^ 2))
      (Set.Iic (x - δ)) :=
    (integrable_poisson_kernel x hε).integrableOn
  have hlim : Filter.Tendsto
      (fun u : ℝ => Real.arctan ((u - x) / ε)) Filter.atBot
      (nhds (-(π / 2))) :=
    tendsto_nhds_of_tendsto_nhdsWithin
      (Real.tendsto_arctan_atBot.comp (tendsto_scaled_atBot x hε))
  have h : ∫ t in Set.Iic (x - δ), ε / ((x - t) ^ 2 + ε ^ 2)
      = Real.arctan ((x - δ - x) / ε) - -(π / 2) :=
    integral_Iic_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have harg : (x - δ - x) / ε = -(δ / ε) := by ring
  rw [h, harg, Real.arctan_neg]
  ring

/-! ### The two-sided tail -/

private theorem compl_Ioo_eq (x δ : ℝ) :
    (Set.Ioo (x - δ) (x + δ))ᶜ
      = Set.Iic (x - δ) ∪ Set.Ici (x + δ) := by
  ext t
  rw [Set.mem_compl_iff, Set.mem_Ioo, Set.mem_union, Set.mem_Iic,
    Set.mem_Ici]
  constructor
  · intro ht
    rcases le_or_gt t (x - δ) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      by_contra hc
      push_neg at hc
      exact ht ⟨h, hc⟩
  · rintro (h | h) ⟨h1, h2⟩
    · linarith
    · linarith

/-- **The exact two-sided tail** of the unnormalised kernel: for
`ε > 0` and `δ > 0`,
`∫_{|t - x| ≥ δ} ε/((x-t)² + ε²) dt = π - 2·arctan (δ/ε)`,
the neighbourhood complement being taken as `(Ioo (x-δ) (x+δ))ᶜ`. -/
theorem setIntegral_poisson_kernel_compl_Ioo (x : ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∫ t in (Set.Ioo (x - δ) (x + δ))ᶜ, ε / ((x - t) ^ 2 + ε ^ 2)
      = π - 2 * Real.arctan (δ / ε) := by
  have hdisj : Disjoint (Set.Iic (x - δ)) (Set.Ici (x + δ)) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    have h1 : t ≤ x - δ := Set.mem_Iic.mp ht
    have h2 : x + δ ≤ t := Set.mem_Ici.mp ht'
    linarith
  have hI1 : IntegrableOn
      (fun t : ℝ => ε / ((x - t) ^ 2 + ε ^ 2))
      (Set.Iic (x - δ)) :=
    (integrable_poisson_kernel x hε).integrableOn
  have hI2 : IntegrableOn
      (fun t : ℝ => ε / ((x - t) ^ 2 + ε ^ 2))
      (Set.Ici (x + δ)) :=
    (integrable_poisson_kernel x hε).integrableOn
  rw [compl_Ioo_eq x δ,
    setIntegral_union hdisj measurableSet_Ici hI1 hI2,
    integral_Ici_eq_integral_Ioi (μ := volume),
    setIntegral_poisson_kernel_Iic x hε,
    setIntegral_poisson_kernel_Ioi x hε]
  ring

/-! ### The normalised density -/

/-- **The exact Lebesgue tail of the Poisson density**: for `ε > 0`
and `δ > 0`,
`∫_{|t - x| ≥ δ} π⁻¹·ε/((x-t)² + ε²) dt = 1 - (2/π)·arctan (δ/ε)`.
This is the statement `FabiusFunction.StieltjesInversion` deferred. -/
theorem setIntegral_poisson_density_compl_Ioo (x : ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∫ t in (Set.Ioo (x - δ) (x + δ))ᶜ,
        π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))
      = 1 - 2 / π * Real.arctan (δ / ε) := by
  rw [MeasureTheory.integral_const_mul,
    setIntegral_poisson_kernel_compl_Ioo x hε hδ, mul_sub,
    inv_mul_cancel₀ Real.pi_ne_zero]
  ring

/-- **The near-field mass**: the complementary reading of the tail.
For `ε > 0` and `δ > 0` the Poisson density puts mass
`(2/π)·arctan (δ/ε)` on `(x - δ, x + δ)`. -/
theorem setIntegral_poisson_density_Ioo (x : ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∫ t in Set.Ioo (x - δ) (x + δ),
        π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))
      = 2 / π * Real.arctan (δ / ε) := by
  have hint : Integrable
      (fun t : ℝ => π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2))) :=
    (integrable_poisson_kernel x hε).const_mul π⁻¹
  have hIoo : MeasurableSet (Set.Ioo (x - δ) (x + δ)) :=
    measurableSet_Ioo
  have hsum := MeasureTheory.integral_add_compl hIoo hint
  rw [integral_poisson_kernel_eq_one x hε,
    setIntegral_poisson_density_compl_Ioo x hε hδ] at hsum
  linarith

private theorem two_div_pi_mul_pi_div_two :
    (2 : ℝ) / π * (π / 2) = 1 := by
  have hr : (2 : ℝ) / π * (π / 2) = π / π * 1 := by ring
  rw [hr, div_self Real.pi_ne_zero, mul_one]

/-- **The tail never vanishes**: for every `ε > 0` and `δ > 0` the
Lebesgue far-field mass of the Poisson density is strictly
positive.  So the limit `0` of
`tendsto_setIntegral_poisson_density_compl_Ioo` is approached and
never attained. -/
theorem setIntegral_poisson_density_compl_Ioo_pos (x : ℝ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    0 < ∫ t in (Set.Ioo (x - δ) (x + δ))ᶜ,
        π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)) := by
  rw [setIntegral_poisson_density_compl_Ioo x hε hδ]
  have h1 : Real.arctan (δ / ε) < π / 2 :=
    Real.arctan_lt_pi_div_two _
  have h2 : (0 : ℝ) < 2 / π := div_pos (by norm_num) Real.pi_pos
  have h3 : 2 / π * Real.arctan (δ / ε) < 2 / π * (π / 2) :=
    mul_lt_mul_of_pos_left h1 h2
  have h4 := two_div_pi_mul_pi_div_two
  linarith

/-- **Calibration at one scale unit**: taking `δ = ε` the Poisson
density puts mass exactly `1/2` outside `(x - ε, x + ε)`.  This
pins the constants `1` and `2/π` of
`setIntegral_poisson_density_compl_Ioo`. -/
theorem setIntegral_poisson_density_compl_Ioo_self (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ t in (Set.Ioo (x - ε) (x + ε))ᶜ,
        π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)) = 1 / 2 := by
  rw [setIntegral_poisson_density_compl_Ioo x hε hε,
    div_self (ne_of_gt hε), Real.arctan_one]
  have hr : (2 : ℝ) / π * (π / 4) = π / π * (1 / 2) := by ring
  rw [hr, div_self Real.pi_ne_zero, one_mul]
  norm_num

/-! ### The `ε → 0⁺` limits -/

private theorem tendsto_div_nhdsGT_zero {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun ε : ℝ => δ / ε)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have hinv : Filter.Tendsto (fun ε : ℝ => ε⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  exact (Filter.Tendsto.const_mul_atTop hδ hinv).congr fun ε =>
    (div_eq_mul_inv δ ε).symm

private theorem tendsto_arctan_div_nhdsGT_zero {δ : ℝ}
    (hδ : 0 < δ) :
    Filter.Tendsto (fun ε : ℝ => Real.arctan (δ / ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (π / 2)) :=
  tendsto_nhds_of_tendsto_nhdsWithin
    (Real.tendsto_arctan_atTop.comp (tendsto_div_nhdsGT_zero hδ))

/-- **The Lebesgue far-field mass vanishes**: for a fixed `x` and a
fixed radius `δ > 0`, the Poisson density's mass outside
`(x - δ, x + δ)` tends to `0` as `ε → 0⁺`.  This is the Lebesgue
counterpart of `Fabius.tendsto_setIntegral_poisson_far`, obtained
from the exact tail rather than from a finite-measure bound. -/
theorem tendsto_setIntegral_poisson_density_compl_Ioo (x : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ t in (Set.Ioo (x - δ) (x + δ))ᶜ,
          π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hlim : Filter.Tendsto
      (fun ε : ℝ => 1 - 2 / π * Real.arctan (δ / ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (1 - 2 / π * (π / 2))) :=
    tendsto_const_nhds.sub
      (tendsto_const_nhds.mul (tendsto_arctan_div_nhdsGT_zero hδ))
  have h5 : (1 : ℝ) - 2 / π * (π / 2) = 0 := by
    rw [two_div_pi_mul_pi_div_two, sub_self]
  rw [h5] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  exact (setIntegral_poisson_density_compl_Ioo x hε' hδ).symm

/-- **Concentration on a neighbourhood**: for a fixed `x` and a
fixed radius `δ > 0`, the Poisson density's mass on
`(x - δ, x + δ)` tends to `1` as `ε → 0⁺`. -/
theorem tendsto_setIntegral_poisson_density_Ioo (x : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ t in Set.Ioo (x - δ) (x + δ),
          π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hlim : Filter.Tendsto
      (fun ε : ℝ => 2 / π * Real.arctan (δ / ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 / π * (π / 2))) :=
    tendsto_const_nhds.mul (tendsto_arctan_div_nhdsGT_zero hδ)
  rw [two_div_pi_mul_pi_div_two] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  exact (setIntegral_poisson_density_Ioo x hε' hδ).symm

/-- **The approximate identity**, in the two halves that phrase
demands.  For every `ε > 0` the normalised Poisson kernel is a
unit total mass on `ℝ` (imported from
`Fabius.integral_poisson_kernel_eq_one`), and for every fixed
neighbourhood radius `δ > 0` its mass on `(x - δ, x + δ)` tends to
`1` as `ε → 0⁺`.  The quantitative content is the exact near-field
mass `setIntegral_poisson_density_Ioo`. -/
theorem poisson_kernel_approximate_identity (x : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    (∀ ε : ℝ, 0 < ε →
        ∫ t : ℝ, π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)) = 1) ∧
      Filter.Tendsto
        (fun ε : ℝ => ∫ t in Set.Ioo (x - δ) (x + δ),
            π⁻¹ * (ε / ((x - t) ^ 2 + ε ^ 2)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  ⟨fun _ hε => integral_poisson_kernel_eq_one x hε,
    tendsto_setIntegral_poisson_density_Ioo x hδ⟩

end Fabius
