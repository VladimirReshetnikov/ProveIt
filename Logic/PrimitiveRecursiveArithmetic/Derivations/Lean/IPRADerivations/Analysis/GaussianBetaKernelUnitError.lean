import IPRADerivations.Analysis.GaussianBetaKernelDecayDampedError

/-!
# The original beta kernel has quadratic error with unit majorant

The actual later beta kernel in the genuine relative telescope is
bounded by one using its original nonnegative numerator and denominator.
The existing cofinal approximation removes only the auxiliary degree;
the requested original decay observation is unchanged.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelUnitError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaKernelDampedRefinement (numerator denominator later_source)
open GaussianBetaKernelRefinement (cutoff value)
open GaussianBetaKernelExponential (kernel)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def errorNumerator (p a b N : PTm n) : PTm n := a*a*unit p+b*b*N
def errorDenominator (p b N : PTm n) : PTm n := b*b*N*unit p

theorem finite_distance (j a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    distanceBounded (kernel a b (cutoff N j)) (kernel a b N) (a*a) (b*b*N) := by
  let K := cutoff N j
  have hs := later_source a b N j h
  have q := GaussianBetaKernelDampedRefinement.denominator_positive (Γ := Γ) b K hs.andE₁ hs.andE₂.andE₁
  have bd := positive_product (Γ := Γ) _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁
  have native : Γ ⊢[PRAAx] le (numerator a b K) (denominator b K) :=
    pw_le_pw K (GaussianRationalMonicReconstruction.monus_le_left (b*K) a)
  have upper := RationalValueBounds.upper_mono _ _ _ _ (a*a) (b*b*N) (positive_product _ _ bd q)
    (GaussianBetaKernelDampedRefinement.original_finite_relative_error a b N j h)
    (le_congr (by dsimp only [GaussianBetaKernelDampedRefinement.relativeNumerator]; ipra_ring)
      (by ipra_ring)
      (mul_le_mul_right (a*a*(b*b*N)) native))
  have opposite := RationalValueBounds.upper_of_order (value a b N) (value a b K) (a*a) (b*b*N)
    (GaussianBetaKernelRefinement.dyadic_order a b N j (GaussianBetaKernelDecayDampedError.full_source a b N h))
  have radius := RationalGaussianNameEmbedding.distance_from_radius _ _ (a*a) (b*b*N) bd
    (RationalValueBounds.radius_of_upper _ _ _ _ upper opposite)
  exact distance_congr
    (GaussianBetaKernelRefinement.kernel_embedding a b K (GaussianBetaKernelDecayDampedError.full_source a b K hs)).eqSymm
    (GaussianBetaKernelRefinement.kernel_embedding a b N (GaussianBetaKernelDecayDampedError.full_source a b N h)).eqSymm
    (.eqRefl _) (.eqRefl _) radius

theorem cofinal_slack (p j a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 decayF p (decayData a b)) (kernel a b N))
      (errorNumerator p a b N) (errorDenominator p b N) (GaussianBetaKernelDomination.cost a) j := by
  have dp := positive_product (Γ := Γ) _ _ (unit_positive j) (unit_positive p)
  have dr := positive_product (Γ := Γ) _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁
  have first := distance_symmetric _ _ _ _ dp (GaussianBetaKernelDecayDampedError.cofinal_original_distance p j a b N h)
  have second := finite_distance j a b N h
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [errorNumerator,errorDenominator,unit]; ipra_ring)
    (by dsimp only [errorDenominator,unit]; ipra_ring)
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ dp dr first second)

/-- Literal original kernel and original requested decay precision. -/
theorem original_kernel_error (p a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    distanceBounded (kernel a b N) (ap2 decayF p (decayData a b))
      (a*a*unit p+b*b*N) (b*b*N*unit p) := by
  have hd := positive_product (Γ := Γ) _ _
    (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁) (unit_positive p)
  have raw := GaussianRationalSlackRemoval.slack_removal_at
    (qsub (ap2 decayF p (decayData a b)) (kernel a b N))
    (errorNumerator p a b N) (errorDenominator p b N) (GaussianBetaKernelDomination.cost a) hd
    (cofinal_slack p (GaussianRationalSlackRemoval.precision
      (qsub (ap2 decayF p (decayData a b)) (kernel a b N))
      (errorNumerator p a b N) (errorDenominator p b N) (GaussianBetaKernelDomination.cost a)) a b N h)
  exact distance_symmetric _ _ _ _ hd raw

theorem original_beta_kernel_unit_majorant_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianBetaKernelLogarithm.source (var 1) (var 2) (var 3) ⟶
      distanceBounded (kernel (var 1) (var 2) (var 3)) (ap2 decayF (var 0) (decayData (var 1) (var 2)))
        ((var 1)*(var 1)*unit (var 0)+(var 2)*(var 2)*(var 3)) ((var 2)*(var 2)*(var 3)*unit (var 0))) :=
  closeUniv 4 (.impI (original_kernel_error _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelUnitError
