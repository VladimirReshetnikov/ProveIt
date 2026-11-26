import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaLateInput
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegralPositiveLower
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayRealSamples
import IPRADerivations.Analysis.Euler.GaussianNamedEulerQuadrature

/-!
# Positive lower bound at a fixed regular real Gamma input

The supplied real-sample guard is the original canonical-axis condition
on the actual input observations. Its decoded native numerator has
exactly zero imaginary part. At one common late input the original
encoded Gamma has the verified one-eighteenth lower bound. Original
named continuity and a single finite scalar gap retain only the
requested output error. The same lower bound transfers to the existing
named improper Euler integral.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaPositiveLower

open_ipra
open GaussianNamedGamma (nameF data)
open GaussianNamedRightHalfPlane (threshold radius numerator denominator actual_late_source)
open GaussianGammaHalfPlaneInputContinuity (modulus)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianNamedRealOrderTransport (upperSlack remove_upper_slack precision)
open RationalValueBounds (upper upper_congr upper_triangle upper_mono upper_of_radius radius_symmetric)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lower : PTm n := GaussianEuclideanDistanceName.fraction one (num 18)
def source (f : PR 2) (x A : PTm n) : Fm PTm n := GaussianNamedRightHalfPlane.source f x A ⋏ realSamples f x
def clock (f : PR 2) (s x A : PTm n) : PTm n := threshold A+succ (modulus s (radius f x) (two*A))
ipra_subst lower
ipra_subst source
ipra_subst clock

/-- Canonical real input samples give actual native imaginary zero,
without identifying an arbitrary raw code with a canonical encoding. -/
theorem decoded_imaginary_zero (f : PR 2) (r x : PTm n) (h : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    ZT.eq (ComplexLogarithmRemainder.im (numerator f r x)) (ZT.ofNat zero) := by
  have real := real_sample_at f x r h
  have code := RationalGaussianEmbedding.canonical_axis_roundtrip _ real.andE₁ real.andE₂
  have fixed := (GaussianRationalConjugation.point_congr code.eqSymm).eqTrans
    ((GaussianRationalConjugation.point_embed _).eqTrans code)
  exact GaussianEulerDecayRealSamples.fixed_raw_imaginary_zero _ fixed

theorem late_input (f : PR 2) (s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianNamedGammaLateInput.input f s (clock f s x A) x A :=
  .andI h.andE₁ (.andI (le_add_right _ _) (le_add_left _ _))

theorem encoded_lower (f : PR 2) (q s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    upper lower (fstT (ap2 GaussianGammaReciprocalInverse.gammaF q
      (GaussianNamedGammaLateInput.encodedData f (clock f s x A) x A))) one (unit q) := by
  have native := actual_late_source f x A (clock f s x A) h.andE₁ (le_add_right _ _)
  exact GaussianEulerIntegralPositiveLower.original_gamma_positive_lower q _ (radius f x) _ (two*A)
    (.andI native (decoded_imaginary_zero f (clock f s x A) x h.andE₂)) (GaussianNameBounds.U_positive f x)

theorem original_lower_budget (f : PR 2) (p s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    upperSlack lower (fstT (ap2 (nameF f) p (data x A))) one (unit p) (num 3) s := by
  let U := unit s
  let P := unit p
  let D := rateDenominator U p s
  have hd := denominator_positive (Γ := Γ) U p s (unit_positive s)
  have distance := GaussianNamedGammaLateInput.original_observations f p s s (clock f s x A) x A (late_input f s x A h)
  have near := upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ (scalar_coordinate_distance _ _ _ _ hd distance))
  have joined := upper_triangle _ _ _ _ _ _ _ (encoded_lower f s s x A h) near
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive s) hd) joined
    (le_congr (by dsimp only [rateNumerator,rateDenominator,D,U,P]; ipra_ring) (.eqRefl _) (le_refl _))

theorem original_gamma_positive_lower (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    upper lower (fstT (ap2 (nameF f) p (data x A))) one (unit p) :=
  remove_upper_slack _ _ _ _ (num 3)
    (original_lower_budget f p (precision lower (fstT (ap2 (nameF f) p (data x A))) (unit p) (num 3)) x A h)

theorem improper_lower_budget (f : PR 2) (p s x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    upperSlack lower (fstT (ap2 (GaussianNamedEulerQuadrature.nameF f) p (data x A))) one (unit p) two s := by
  have identity := GaussianNameEquivalence.cross_symm _ _ _ _
    (GaussianNamedEulerQuadrature.original_named_Euler_integral_is_Gamma f x A h.andE₁)
  have distance := GaussianNameEquivalence.cross_at _ _ _ _ s p identity
  have den := positive_product _ _ (unit_positive (Γ := Γ) s) (unit_positive p)
  have near := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ den distance)
  have joined := upper_triangle _ _ _ _ _ _ _ (original_gamma_positive_lower f s x A h) near
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive s) den) joined
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _))

theorem original_improper_positive_lower (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    upper lower (fstT (ap2 (GaussianNamedEulerQuadrature.nameF f) p (data x A))) one (unit p) :=
  remove_upper_slack _ _ _ _ two
    (improper_lower_budget f p (precision lower
      (fstT (ap2 (GaussianNamedEulerQuadrature.nameF f) p (data x A))) (unit p) two) x A h)

theorem original_named_real_Gamma_one_eighteenth_lower_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 1) (var 2) ⟶ upper lower (fstT (ap2 (nameF f) (var 0) (data (var 1) (var 2)))) one (unit (var 0))) :=
  closeUniv 3 (.impI (original_gamma_positive_lower f _ _ _ Prf.hyp0))
theorem original_named_real_Euler_integral_one_eighteenth_lower_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 1) (var 2) ⟶ upper lower
      (fstT (ap2 (GaussianNamedEulerQuadrature.nameF f) (var 0) (data (var 1) (var 2)))) one (unit (var 0))) :=
  closeUniv 3 (.impI (original_improper_positive_lower f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaPositiveLower
