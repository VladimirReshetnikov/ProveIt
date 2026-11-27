import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteEulerLateInput
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaLateInput
import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.FiniteEstimates.GaussianEulerSharpAllDegrees
import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerIntegralGammaIdentification

/-!
# The literal sharp Euler rate on an original regular complex name

At one common actual late input sample, use the original all-degree
finite Euler bound and the original improper-integral/Gamma identity.
The original input disk is exactly U(f,x), so both numerical leading
terms keep that radius. A finite integer gap removes only the auxiliary
observations; both requested named-output errors remain independent.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpNamedRate

open_ipra
open GaussianNamedRightHalfPlane (radius numerator denominator threshold actual_late_source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianReconstructionRoots (distance_triangle)
open GaussianEulerSharpResidualAssembly (boundNumerator boundDenominator)
open GaussianBetaContiguousUpperTailBudget (fixedNumerator fixedDenominator fixed_denominator_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (f : PR 2) (x A N : PTm n) : Fm PTm n := GaussianNamedRightHalfPlane.source f x A ⋏ le two N
def finitePoint (f : PR 2) (p x A N : PTm n) : PTm n :=
  ap2 (GaussianNamedFiniteEuler.nameF f) p (GaussianNamedFiniteEuler.data x A N)
def gammaPoint (f : PR 2) (v x A : PTm n) : PTm n := ap2 (GaussianNamedGamma.nameF f) v (GaussianNamedGamma.data x A)
def clock (f : PR 2) (t x A N : PTm n) : PTm n := threshold A+
  succ (GaussianNamedFiniteEuler.modulus t (radius f x) (two*A) N)+
  succ (GaussianGammaHalfPlaneInputContinuity.modulus t (radius f x) (two*A))
def baseNumerator (q0 R N : PTm n) : PTm n := GaussianEulerSharpDegreeSchedule.coefficient R*fixedDenominator q0 N+fixedNumerator q0 R N*N
def baseDenominator (q0 N : PTm n) : PTm n := N*fixedDenominator q0 N

theorem join_encoded_radius (a b c X Y U : PTm n)
    (hY : Γ ⊢[PRAAx] le one Y) (hU : Γ ⊢[PRAAx] le one U)
    (hab : Γ ⊢[PRAAx] distanceBounded a b (boundNumerator X Y U U) (boundDenominator Y U U))
    (hbc : Γ ⊢[PRAAx] distanceBounded b c (U+U) (U*U)) : Γ ⊢[PRAAx]
    distanceBounded a c (X*U+num 6*Y) (Y*U) := by
  have h₁ := positive_product _ _ hY (positive_product _ _ hU hU)
  have h₂ := positive_product _ _ hU hU
  have total := distance_triangle _ _ _ _ _ _ _ h₁ h₂ hab hbc
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ h₁ h₂) (positive_product _ _ hY hU)
    (le_of_eq_add (d := two*Y*Y*U*U*U*U) (by dsimp only [boundNumerator,boundDenominator]; ipra_ring)) total

theorem cofinal_observations (f : PR 2) (t p v q0 x A N : PTm n) (h : Γ ⊢[PRAAx] source f x A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint f p x A N) (gammaPoint f v x A)
      (GaussianEulerSharpFiniteRate.numerator p v q0 (radius f x) N*unit t+
        num 12*GaussianEulerSharpFiniteRate.denominator p v q0 N)
      (GaussianEulerSharpFiniteRate.denominator p v q0 N*unit t) := by
  let r := clock f t x A N
  let R := radius f x
  let z := numerator f r x
  let B := denominator f r x
  let X := baseNumerator q0 R N
  let Y := baseDenominator q0 N
  let U := unit t
  have hN : Γ ⊢[PRAAx] le one N := le_trans (le_succ_self one) h.andE₂
  have hY : Γ ⊢[PRAAx] le one Y := positive_product _ _ hN (fixed_denominator_positive q0 N)
  have hU : Γ ⊢[PRAAx] le one U := unit_positive t
  have hP := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) v
  have hm : Γ ⊢[PRAAx] le (threshold A) r :=
    le_trans (le_add_right _ _) (le_add_right _ _)
  have hf : Γ ⊢[PRAAx] le (succ (GaussianNamedFiniteEuler.modulus t R (two*A) N)) r :=
    le_trans (le_add_left _ _) (le_add_right _ _)
  have hg : Γ ⊢[PRAAx] le (succ (GaussianGammaHalfPlaneInputContinuity.modulus t R (two*A))) r := le_add_left _ _
  have late := actual_late_source f x A r h.andE₁ hm
  have rawFinite := GaussianNamedFiniteEulerLateInput.original_observations f p t t r x A N (.andI h.andE₁ hN) hm hf
  have finite : Γ ⊢[PRAAx] distanceBounded (GaussianEulerSharpAllDegrees.finitePoint t z B N) (finitePoint f p x A N)
      (U+two*unit p) (U*unit p) := by
    apply distance_symmetric _ _ _ _ (positive_product _ _ hU hP)
    exact distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive _ _ _ hU)
      (positive_product _ _ hU hP) (le_of_eq_add (d := zero) (by unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator; ipra_ring)) rawFinite
  have sharp : Γ ⊢[PRAAx] distanceBounded (GaussianEulerSharpAllDegrees.finitePoint t z B N)
      (GaussianEulerSharpFiniteRate.improperPoint t z R B (two*A)) (boundNumerator X Y U U) (boundDenominator Y U U) :=
    GaussianEulerSharpAllDegrees.original_sharp_bound t t q0 z R B (two*A) N (.andI late h.andE₂)
  have identity := GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B (two*A)
    (.andI late (GaussianNameBounds.U_positive f x))
  have middle := join_encoded_radius _ _ _ X Y U hY hU sharp (GaussianNameEquivalence.cross_at _ _ _ _ t t identity)
  have rawGamma := GaussianNamedGammaLateInput.original_observations f v t t r x A (.andI h.andE₁ (.andI hm hg))
  have gamma : Γ ⊢[PRAAx] distanceBounded (ap2 GaussianGammaReciprocalInverse.gammaF t (GaussianNamedGammaLateInput.encodedData f r x A))
      (gammaPoint f v x A) (U+num 4*unit v) (U*unit v) := by
    apply distance_symmetric _ _ _ _ (positive_product _ _ hU hV)
    exact distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive _ _ _ hU)
      (positive_product _ _ hU hV) (le_of_eq_add (d := two*U*U*unit v*unit v)
        (by unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator; ipra_ring)) rawGamma
  exact GaussianEulerSharpResidualAssembly.sampler_distance _ _ _ _ X Y (unit p) (unit v) U hY hP hV hU finite middle gamma

theorem original_sharp_bound (f : PR 2) (p v q0 x A N : PTm n) (h : Γ ⊢[PRAAx] source f x A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint f p x A N) (gammaPoint f v x A)
      (GaussianEulerSharpFiniteRate.numerator p v q0 (radius f x) N) (GaussianEulerSharpFiniteRate.denominator p v q0 N) := by
  let a := finitePoint f p x A N
  let b := gammaPoint f v x A
  let X := GaussianEulerSharpFiniteRate.numerator p v q0 (radius f x) N
  let Y := GaussianEulerSharpFiniteRate.denominator p v q0 N
  let t := GaussianRationalSlackRemoval.precision (qsub a b) X Y (num 12)
  have hN : Γ ⊢[PRAAx] le one N := le_trans (le_succ_self one) h.andE₂
  have hY : Γ ⊢[PRAAx] le one Y := positive_product _ _
    (positive_product _ _ hN (fixed_denominator_positive q0 N)) (positive_product _ _ (unit_positive p) (unit_positive v))
  exact GaussianRationalSlackRemoval.slack_removal_at (qsub a b) X Y (num 12) hY (cofinal_observations f t p v q0 x A N h)

theorem original_sharp_Euler_rate_at_named_complex_input_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source f (var 3) (var 4) (var 5) ⟶
      distanceBounded (finitePoint f (var 0) (var 3) (var 4) (var 5)) (gammaPoint f (var 1) (var 3) (var 4))
        (GaussianEulerSharpFiniteRate.numerator (var 0) (var 1) (var 2) (radius f (var 3)) (var 5))
        (GaussianEulerSharpFiniteRate.denominator (var 0) (var 1) (var 2) (var 5))) :=
  closeUniv 6 (.impI (original_sharp_bound f _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSharpNamedRate
