import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.Named.GaussianNamedEulerLogarithmicIncrementBinding
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.EndpointRates.GaussianNamedDifferenceQuotientApproximation
import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.GaussianEulerLogarithmicDerivative

/-!
# All logarithmic Euler derivatives at a fixed certified complex name

The original named input can be any fixed primitive-recursive complex name.
A native nonzero increment is supplied after the basepoint modulus has
been computed. The two endpoint cutoffs and the slope use a common late
decoded basepoint. The actual difference quotient of the two original
named evaluators has the native derivative rate with independent queries.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicDerivative

open_ipra
open GaussianNamedRightHalfPlane (radius)
open GaussianNamedGammaIncrementInput (incrementF incrementData)
open GaussianNamedEulerLogarithmicIncrementBinding (baseClock baseNumerator baseDenominator shiftedNumerator shiftedDatum
  base_certificate frozen_base_rate frozen_shifted_rate frozen_slope_rate)
open GaussianNamedEulerLogarithmicFrozenRate (frozenData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive rate_at)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "Named" => GaussianNamedEulerLogarithmicImproper.nameF
local notation "ndata" => GaussianNamedEulerLogarithmicImproper.data
local notation "QF" f:max => GaussianNamedDifferenceQuotient.nameF (Named (incrementF f)) (Named f)
local notation "IQ" => GaussianNamedDifferenceQuotient.nameF I I
local notation "certificate" => GaussianEulerLowerPowerCoefficients.source

def incrementModulus (f : PR 2) (p j x A : PTm n) : PTm n :=
  GaussianEulerLogarithmicContinuity.modulus (succ p+num 6) (succ j) (radius f x) (two*A)
def source (f : PR 2) (p j x A h D : PTm n) : Fm PTm n :=
  GaussianNamedRightHalfPlane.source f x A ⋏
    (le one D ⋏ (le one (ComplexLogarithmRemainder.normSq h) ⋏
      bounded (ofGaussian h D) one (incrementModulus f p j x A)))
def readIndex (p D : PTm n) : PTm n := GaussianFastValueCut.exponent (num 19*D+num 9) (succ p)
def quotientData (f : PR 2) (j x A h D : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data (Named (incrementF f)) (Named f)
    (ndata j (incrementData x h D) (two*A)) (ndata j x A) h D

ipra_subst incrementModulus
ipra_subst source
ipra_subst quotientData

theorem native_source (f : PR 2) (s p j x A h D : PTm n) (hs : Γ ⊢[PRAAx] source f p j x A h D) :
    Γ ⊢[PRAAx] GaussianEulerLogarithmicDerivative.source (succ p) j (baseNumerator f s j x A)
      (radius f x) (baseDenominator f s j x A) (two*A) h D :=
  .andI (.andI (base_certificate f s j x A hs.andE₁) (.andI hs.andE₂.andE₁ hs.andE₂.andE₂.andE₂)) hs.andE₂.andE₂.andE₁

theorem increment_source (f : PR 2) (p j x A h D : PTm n) (hs : Γ ⊢[PRAAx] source f p j x A h D) :
    Γ ⊢[PRAAx] GaussianNamedGammaIncrementInput.source f x A h D := by
  have native := native_source f zero p j x A h D hs
  have path := GaussianEulerLogarithmicContinuity.path_source (succ p+num 6) (succ j)
    (baseNumerator f zero j x A) (radius f x) (baseDenominator f zero j x A) (two*A) h D native.andE₁
  have four : Γ ⊢[PRAAx] le one (num 4) := le_of_eq_add (d := num 3) (by ipra_ring)
  have pos := positive_product _ _ four hs.andE₁.andE₂.andE₁
  have wide := positive_product _ _ four native.andE₁.andE₁.andE₁
  have small := bounded_radius_mono (ofGaussian h D) one (num 4*(two*A)) one (num 4*A) wide pos
    (le_of_eq_add (d := num 4*A) (by ipra_ring)) path.andE₂.andE₂
  exact .andI hs.andE₁ (.andI hs.andE₂.andE₁ small)

theorem quotient_input (f : PR 2) (p j x A h D : PTm n) (hs : Γ ⊢[PRAAx] source f p j x A h D) :
    Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.input (Named (incrementF f)) (Named f)
      (ndata j (incrementData x h D) (two*A)) (ndata j x A) h D := by
  have shifted := GaussianNamedGammaIncrementInput.original_source f x A h D (increment_source f p j x A h D hs)
  exact .andI (GaussianNamedEulerLogarithmicImproper.name_regular (incrementF f) j (incrementData x h D) (two*A) shifted)
    (.andI (GaussianNamedEulerLogarithmicImproper.name_regular f j x A hs.andE₁) (.andI hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁))

theorem quotient_regular (f : PR 2) (p j x A h D : PTm n) (hs : Γ ⊢[PRAAx] source f p j x A h D) :
    Γ ⊢[PRAAx] pointCN (QF f) (quotientData f j x A h D) :=
  GaussianNamedDifferenceQuotient.name_regular (Named (incrementF f)) (Named f) _ _ h D (quotient_input f p j x A h D hs)

theorem original_observations (f : PR 2) (q v p j x A h D : PTm n) (hs : Γ ⊢[PRAAx] source f p j x A h D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (QF f) q (quotientData f j x A h D))
      (ap2 (Named f) v (ndata (succ j) x A)) (rateNumerator one (unit p) q v) (rateDenominator (unit p) q v) := by
  let s := readIndex p D
  let X := ndata j (incrementData x h D) (two*A)
  let Y := ndata j x A
  let E := shiftedDatum f s j x A h D
  let F := frozenData f j x A (baseClock f s j x A)
  let G := frozenData f (succ j) x A (baseClock f s j x A)
  let z := baseNumerator f s j x A
  let B := baseDenominator f s j x A
  let R := radius f x
  let S := unit s
  let T := unit (succ p)
  let J := unit p
  let Q := unit q
  let V := unit v
  let Z := T*S*Q*V
  have native := native_source f s p j x A h D hs
  have exactShift := GaussianEulerLogarithmicContinuity.shifted_certificate (succ p+num 6) (succ j) z R B (two*A) h D native.andE₁
  have shiftRate := frozen_shifted_rate f s j x A h D (increment_source f p j x A h D hs) exactShift
  have baseRate := frozen_base_rate f s j x A hs.andE₁
  have slopeRate := frozen_slope_rate f s j x A hs.andE₁
  have hS := unit_positive (Γ := Γ) s
  have hT := unit_positive (Γ := Γ) (succ p)
  have hQ := unit_positive (Γ := Γ) q
  have hV := unit_positive (Γ := Γ) v
  have pos : Γ ⊢[PRAAx] le one Z := positive_product _ _ (positive_product _ _ (positive_product _ _ hT hS) hQ) hV
  have raw := GaussianNamedDifferenceQuotientApproximation.independent_at (Named (incrementF f)) (Named f) I I
    q s s X Y E F h D (num 5+num 5) S (num 5) S (quotient_input f p j x A h D hs) hS hS shiftRate baseRate
  have rawDen := GaussianNamedDifferenceQuotientApproximation.denominator_positive S S q s s hS hS
  have first := distance_radius_mono _ _ _ _ ((num 17*D*Q+S)*(T*V)) Z rawDen pos
    (le_of_eq_add (d := zero) (by dsimp only [GaussianNamedDifferenceQuotientApproximation.numerator,
      GaussianNamedDifferenceQuotientApproximation.denominator,S,T,Q,V,Z]; ipra_ring)) raw
  have read := GaussianNamedDifferenceQuotient.independent_readback I I s s s E F h D
    (GaussianEulerLogarithmicDerivative.quotient_input (succ p) j z R B (two*A) h D native)
  have readDen := GaussianNamedDifferenceQuotient.denominator_positive (Γ := Γ) s s s
  have second := distance_radius_mono _ _ _ _ ((one+two*D)*(T*Q*V)) Z readDen pos
    (le_of_eq_add (d := zero) (by dsimp only [GaussianNamedDifferenceQuotient.numerator,
      GaussianNamedDifferenceQuotient.denominator,S,T,Q,V,Z]; ipra_ring))
    (distance_symmetric _ _ _ _ readDen read)
  have nativeRate := GaussianEulerLogarithmicDerivative.original_observations s s (succ p) j z R B (two*A) h D native
  have third := distance_radius_mono _ _ _ _ ((S+two*T)*(Q*V)) Z (denominator_positive T s s hT) pos
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,S,T,Q,V,Z]; ipra_ring)) nativeRate
  have slope := rate_at (Named f) I (ndata (succ j) x A) G (num 5) S v s slopeRate
  have slopeDen := denominator_positive S v s hS
  have fourth := distance_radius_mono _ _ _ _ ((num 6*V+S)*(T*Q)) Z slopeDen pos
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,S,T,Q,V,Z]; ipra_ring))
    (distance_symmetric _ _ _ _ slopeDen slope)
  have all := distance_triangle_same _ _ _ _ _ _ pos first
    (distance_triangle_same _ _ _ _ _ _ pos second (distance_triangle_same _ _ _ _ _ _ pos third fourth))
  have pays : Γ ⊢[PRAAx] le ((num 19*D+num 9)*T) S := GaussianFastValueCut.query_budget _ _
  have dyadic : 𝔞 T = 𝔞(two*J) := natEq (GaussianRationalHalfAngleRecovery.unit_succ (Γ := Γ) p)
  exact distance_radius_mono _ _ _ _ _ _ pos (denominator_positive J q v (unit_positive p)) (by
    dsimp only [rateNumerator,rateDenominator,Z,J,Q,V]
    ipra_le 𝔞(unit p)*(𝔞(unit q)*𝔞(unit v))^2*sl pays using
      dsimp only [T,S,J,Q,V] at dyadic ⊢
      rw [dyadic]
      ring) all

theorem original_derivative_rate (f : PR 2) (p j x A h D : PTm n) (hs : Γ ⊢[PRAAx] source f p j x A h D) :
    Γ ⊢[PRAAx] independentRate (QF f) (Named f) (quotientData f j x A h D) (ndata (succ j) x A) one (unit p) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hh : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh p) (sh j) (sh x) (sh A) (sh h) (sh D) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa [independentRate,Syn.shift,sh,one] using
    original_observations f (var 1) (var 0) (sh p) (sh j) (sh x) (sh A) (sh h) (sh D) hh

theorem actual_original_improper_logarithmic_derivative_at_fixed_name_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        independentRate (QF f) (Named f) (quotientData f (var 1) (var 2) (var 3) (var 4) (var 5))
          (ndata (succ (var 1)) (var 2) (var 3)) one (unit (var 0))) :=
  closeUniv 6 (.impI (original_derivative_rate f _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicDerivative
