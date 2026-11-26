import IPRADerivations.Analysis.Euler.Logarithms.GaussianNamedEulerLogarithmicFrozenRate
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaIncrementInput
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition

/-!
# Common frozen base point for a named integral and its native increment

There are separate clocks for the original and the shifted complex name.
The base clock is late for both adjacent logarithmic orders. The shifted
clock is late for its own certificate, and both clocks pay the modulus at
the exact shift of the decoded base value. This lets the native quotient
use one and the same base value at both its endpoints and its slope.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicIncrementBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlane (threshold radius numerator denominator actual_late_source)
open GaussianNamedGammaIncrementInput (incrementF incrementData)
open GaussianEulerLogarithmicContinuity (modulus modulus_positive)
open GaussianNamedEulerLogarithmicFrozenRate (frozenData)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianNamedInverseRate (independentRate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "idata" => GaussianEulerLogarithmicImproperName.data
local notation "Named" => GaussianNamedEulerLogarithmicImproper.nameF
local notation "ndata" => GaussianNamedEulerLogarithmicImproper.data
local notation "certificate" => GaussianEulerLowerPowerCoefficients.source
local notation "shiftInput" => GaussianNamedGammaIncrementInput.source

def lateClock (f : PR 2) (s j x A : PTm n) : PTm n :=
  threshold A+succ (modulus s j (radius f x) (two*A))
def shiftDemand (f : PR 2) (s j x A : PTm n) : PTm n :=
  modulus s j (radius f x+one) (two*(two*A))
def baseClock (f : PR 2) (s j x A : PTm n) : PTm n :=
  lateClock f s j x A+lateClock f s (succ j) x A+succ (shiftDemand f s j x A)
def shiftClock (f : PR 2) (s j x A h D : PTm n) : PTm n :=
  lateClock (incrementF f) s j (incrementData x h D) (two*A)+succ (shiftDemand f s j x A)
def baseNumerator (f : PR 2) (s j x A : PTm n) : PTm n := numerator f (baseClock f s j x A) x
def baseDenominator (f : PR 2) (s j x A : PTm n) : PTm n := denominator f (baseClock f s j x A) x
def shiftedNumerator (f : PR 2) (s j x A h D : PTm n) : PTm n :=
  shifted (baseNumerator f s j x A) (baseDenominator f s j x A) h D
def shiftedDatum (f : PR 2) (s j x A h D : PTm n) : PTm n :=
  idata j (shiftedNumerator f s j x A h D) (radius f x+one) (baseDenominator f s j x A*D) (two*(two*A))

theorem base_threshold (f : PR 2) (s j x A : PTm n) : Γ ⊢[PRAAx] le (threshold A) (baseClock f s j x A) :=
  le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))

theorem base_certificate (f : PR 2) (s j x A : PTm n) (hs : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A) :
    Γ ⊢[PRAAx] certificate (baseNumerator f s j x A) (radius f x) (baseDenominator f s j x A) (two*A) :=
  actual_late_source f x A (baseClock f s j x A) hs (base_threshold f s j x A)

theorem frozen_base_rate (f : PR 2) (s j x A : PTm n) (hs : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A) :
    Γ ⊢[PRAAx] independentRate (Named f) I (ndata j x A) (frozenData f j x A (baseClock f s j x A)) (num 5) (unit s) :=
  GaussianNamedEulerLogarithmicFrozenRate.frozen_rate f s j x A _ (.andI hs
    (.andI (base_threshold f s j x A) (le_trans (le_add_left _ _) (le_trans (le_add_right _ _) (le_add_right _ _)))))

theorem frozen_slope_rate (f : PR 2) (s j x A : PTm n) (hs : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A) :
    Γ ⊢[PRAAx] independentRate (Named f) I (ndata (succ j) x A) (frozenData f (succ j) x A (baseClock f s j x A))
      (num 5) (unit s) :=
  GaussianNamedEulerLogarithmicFrozenRate.frozen_rate f s (succ j) x A _ (.andI hs
    (.andI (base_threshold f s j x A) (le_trans (le_add_left _ _) (le_trans (le_add_left _ _) (le_add_right _ _)))))

private theorem paired_budget (m r k : PTm n) (hr : Γ ⊢[PRAAx] le (succ m) r) (hk : Γ ⊢[PRAAx] le (succ m) k) :
    Γ ⊢[PRAAx] le ((unit k+unit r)*m) (one*(unit k*unit r)) := by
  have amp : Γ ⊢[PRAAx] le m (unit m) := LeanProofs.IPRA.Foundations.DyadicGain.amplitude_absorb m
  have power : Γ ⊢[PRAAx] unit (succ m) ≐ unit m*two := pw_succ two m
  have pays : Γ ⊢[PRAAx] le (m*two) (unit (succ m)) :=
    le_congr (.eqRefl _) power.eqSymm (mul_le_mul_right two amp)
  have left := mul_le_mul_right (unit k) (le_trans pays (unit_monotone hr))
  have right := mul_le_mul_right (unit r) (le_trans pays (unit_monotone hk))
  exact RationalValueBounds.positive_cancel RationalAlgebra.two_positive
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ left right))

theorem exact_shift_distance (f : PR 2) (s j x A h D : PTm n)
    (hs : Γ ⊢[PRAAx] shiftInput f x A h D) : Γ ⊢[PRAAx]
    distanceBounded
      (ofGaussian (numerator (incrementF f) (shiftClock f s j x A h D) (incrementData x h D))
        (denominator (incrementF f) (shiftClock f s j x A h D) (incrementData x h D)))
      (ofGaussian (shiftedNumerator f s j x A h D) (baseDenominator f s j x A*D))
      one (shiftDemand f s j x A) := by
  let k := shiftClock f s j x A h D
  let r := baseClock f s j x A
  let m := shiftDemand f s j x A
  let v := ofGaussian (shiftedNumerator f s j x A h D) (baseDenominator f s j x A*D)
  have hD := hs.andE₂.andE₁
  have base := base_certificate f s j x A hs.andE₁
  have valid : Γ ⊢[PRAAx] GaussianRationalHorner.canonical v :=
    ofGaussian_canonical _ _ (positive_product _ _ base.andE₂.andE₁.andE₁ hD)
  have near := GaussianNamedGammaIncrementInput.sample_to_frozen f k r x h D hs.andE₁.andE₁ hD
  have old : Γ ⊢[PRAAx] le one (unit k*unit r) := positive_product _ _ (unit_positive k) (unit_positive r)
  have recoded := GaussianFastValueCut.recode_distance_bound _ v _ _ old near
  have close := distance_congr (.eqRefl _) (GaussianExponentialReference.recode_fixed v valid) (.eqRefl _) (.eqRefl _) recoded
  exact distance_radius_mono _ _ _ _ one m old (modulus_positive s j (radius f x+one) (two*(two*A)))
    (paired_budget m r k (le_add_left _ _) (le_add_left _ _)) close

theorem frozen_shifted_rate (f : PR 2) (s j x A h D : PTm n)
    (hs : Γ ⊢[PRAAx] shiftInput f x A h D)
    (hv : Γ ⊢[PRAAx] certificate (shiftedNumerator f s j x A h D) (radius f x+one)
      (baseDenominator f s j x A*D) (two*(two*A))) :
    Γ ⊢[PRAAx] independentRate (Named (incrementF f)) I (ndata j (incrementData x h D) (two*A))
      (shiftedDatum f s j x A h D) (num 5+num 5) (unit s) := by
  let g := incrementF f
  let y := incrementData x h D
  let V := two*A
  let k := shiftClock f s j x A h D
  have actual := GaussianNamedGammaIncrementInput.original_source f x A h D hs
  have late : Γ ⊢[PRAAx] le (threshold V) k := le_trans (le_add_right _ _) (le_add_right _ _)
  have frozen := actual_late_source g y V k actual late
  have rate := GaussianEulerLogarithmicMixedParameterRate.original_mixed_parameter_rate s j
    (shiftedNumerator f s j x A h D) (numerator g k y) (radius f x+one) (radius g y)
    (baseDenominator f s j x A*D) (denominator g k y) (two*V) (two*V)
    (.andI hv (.andI frozen (exact_shift_distance f s j x A h D hs)))
  have first := GaussianNamedEulerLogarithmicFrozenRate.frozen_rate g s j y V k
    (.andI actual (.andI late (le_trans (le_add_left _ _) (le_add_right _ _))))
  exact GaussianNamedRateComposition.same_denominator (Named g) I I (ndata j y V)
    (frozenData g j y V k) (shiftedDatum f s j x A h D) (num 5) (unit s) (num 5) (unit_positive s) first rate

theorem actual_original_logarithmic_frozen_shifted_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((shiftInput f (var 2) (var 3) (var 4) (var 5) ⋏
      certificate (shiftedNumerator f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (radius f (var 2)+one)
        (baseDenominator f (var 0) (var 1) (var 2) (var 3)*var 5) (two*(two*var 3))) ⟶
      independentRate (Named (incrementF f)) I (ndata (var 1) (incrementData (var 2) (var 4) (var 5)) (two*var 3))
        (shiftedDatum f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (num 5+num 5) (unit (var 0))) :=
  closeUniv 6 (.impI (frozen_shifted_rate f _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicIncrementBinding
