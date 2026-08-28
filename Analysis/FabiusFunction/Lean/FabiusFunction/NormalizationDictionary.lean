import FabiusFunction.RandomSeriesLaw

/-!
# The canonical normalization dictionary

The Thue–Morse volume's roadmap carries a *Canonical normalization
theorem* obligation: the repository's historical manuscripts use
several Fourier conventions, and a single promoted theorem should fix
the convention and derive every rescaling between the bounded Fabius
function `F`, Rvachev's up-function, the dyadic sinc product `Q_∞`,
and the characteristic function of the random series `Y_∞`, so that
sign and `2π` factors never have to be reconstructed at a use site.

This module is that theorem.  The convention is Mathlib-facing:
`rvachevFourier F z = ∫ up(t)·e^{-2πitz} dt` is the `2π`-in-the-
exponent transform, and `charFun` is Mathlib's characteristic function
`E[e^{i⟨t,·⟩}]`.  The dictionary's four entries are:

1. the fold `up(x) = F(1 - |x|)` for every real `x` — the
   `F ↔ up` rescaling with the absolute-value normalization;
2. `Û(z) = Q_∞(z)` — the transform is the dyadic sinc product,
   for every complex `z`;
3. `charFun μ_up t = Û(t/(2π))` — Mathlib's characteristic function
   of the up-measure is the transform at the rescaled frequency;
4. `E[e^{itY_∞}] = e^{it/2}·Û(t/(4π))` — the random series adds the
   midpoint phase and halves the frequency again.

Each entry exists as a named theorem
(`rvachevUp_eq_weightedSumCDF` + `weightedSumCDF_eq_fabiusReal`,
`rvachevFourier_eq_product`, `rvachevMeasure_charFun_pos`,
`charFun_weightedSumDistribution`); the dictionary bundles them into
the single named package the roadmap asks for.
-/

set_option autoImplicit false

open MeasureTheory Complex

namespace Fabius

open ProbabilityRepresentation

/-- The `F ↔ up` rescaling in its uniform absolute-value form:
`up(x) = F(1 - |x|)` for every real `x`. -/
theorem rvachevUp_eq_fabiusReal_one_sub_abs (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) :
    rvachevUp F x = fabiusReal F (1 - |x|) := by
  rw [rvachevUp_eq_weightedSumCDF F hF, weightedSumCDF_eq_fabiusReal F hF]

/-- **The canonical normalization dictionary** (the Thue–Morse
roadmap's obligation, packaged): with the convention
`Û(z) = ∫ up(t)·e^{-2πitz} dt` and Mathlib's characteristic function,
all four rescalings between the bounded function, the up-function, the
dyadic sinc product, and the two characteristic functions hold
simultaneously — `up = F(1-|·|)`, `Û = Q_∞`,
`charFun μ_up = Û(·/(2π))`, and
`E[e^{itY_∞}] = e^{it/2}·Û(t/(4π))`. -/
theorem normalization_dictionary (F : BoundedFabius) (hF : IsFabius F) :
    (∀ x : ℝ, rvachevUp F x = fabiusReal F (1 - |x|)) ∧
      (∀ z : ℂ, rvachevFourier F z = rvachevFourierProduct z) ∧
      (∀ t : ℝ, charFun (rvachevMeasure F) t =
        rvachevFourier F ((t : ℂ) / (2 * Real.pi))) ∧
      (∀ t : ℝ, charFun weightedSumDistribution t =
        cexp (((2⁻¹ * t : ℝ) : ℂ) * I) *
          rvachevFourier F (((2⁻¹ * t : ℝ) : ℂ) / (2 * Real.pi))) :=
  ⟨rvachevUp_eq_fabiusReal_one_sub_abs F hF,
    rvachevFourier_eq_product F hF,
    rvachevMeasure_charFun_pos F hF,
    charFun_weightedSumDistribution F hF⟩

end Fabius
