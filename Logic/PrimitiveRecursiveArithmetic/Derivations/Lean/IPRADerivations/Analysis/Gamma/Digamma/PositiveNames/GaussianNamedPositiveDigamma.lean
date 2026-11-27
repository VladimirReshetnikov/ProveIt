import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaFirstCrossing
import IPRADerivations.Analysis.Gamma.EulerProducts.Derivatives.GaussianNamedGammaEulerFirstDerivative
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelUniform

/-!
# The original normalized digamma on named positive real inputs

The name multiplies the order-one Euler integral by the certified reciprocal
of the original Gamma name. Gamma times this normalized name is exactly
the original derivative, including at its zeros.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveDigamma

open_ipra
open GaussianBoundedInverseApartness (ones_equivalent)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative multiply_one_left
  oneF one_fast zeroF zero_fast zero_at)
open GaussianNamedGammaFirstCrossing (inverseClock positive_gamma_apart)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (qzero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev source (f : PR 2) (x A : PTm n) : Fm PTm n :=
  GaussianNamedGammaPositiveLower.source f x A

abbrev derivativeF (f : PR 2) : PR 2 := GaussianNamedEulerLogarithmicImproper.nameF f

abbrev derivativeData (x A : PTm n) : PTm n := GaussianNamedEulerLogarithmicImproper.data one x A

abbrev inverseF (f : PR 2) : PR 2 := GaussianNameReciprocal.nameF (GaussianNamedGamma.nameF f)

abbrev inverseData (x A : PTm n) : PTm n :=
  GaussianNameReciprocal.nameData inverseClock (GaussianNamedGamma.data x A)

def nameF (f : PR 2) : PR 2 := multiplyF (inverseF f) (derivativeF f)

def data (f : PR 2) (x A : PTm n) : PTm n :=
  multiplyData (inverseF f) (derivativeF f) (inverseData x A) (derivativeData x A)

ipra_subst data [derivativeData, inverseData, inverseClock, one, two]

theorem inverse_input (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianNameReciprocal.input (GaussianNamedGamma.nameF f) inverseClock (GaussianNamedGamma.data x A) :=
  .andI (GaussianNamedGamma.name_regular f x A h.andE₁) (positive_gamma_apart f x A h)

theorem inverse_regular (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    pointCN (inverseF f) (inverseData x A) :=
  GaussianNameReciprocal.name_fast (GaussianNamedGamma.nameF f) inverseClock (GaussianNamedGamma.data x A)
    (inverse_input f x A h).andE₁ (inverse_input f x A h).andE₂

theorem derivative_regular (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    pointCN (derivativeF f) (derivativeData x A) :=
  GaussianNamedEulerLogarithmicImproper.name_regular f one x A h.andE₁

theorem name_regular (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    pointCN (nameF f) (data f x A) :=
  multiply_fast (inverseF f) (derivativeF f) (inverseData x A) (derivativeData x A)
    (inverse_regular f x A h) (derivative_regular f x A h)

theorem gamma_times_digamma (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (GaussianNamedGamma.nameF f) (nameF f)) (derivativeF f)
      (multiplyData (GaussianNamedGamma.nameF f) (nameF f) (GaussianNamedGamma.data x A) (data f x A))
      (derivativeData x A) := by
  let G := GaussianNamedGamma.nameF f
  let g := GaussianNamedGamma.data x A
  let I := inverseF f
  let i := inverseData x A
  let D := derivativeF f
  let d := derivativeData x A
  let GI := multiplyF G I
  let gi := multiplyData G I g i
  have hG := (inverse_input f x A h).andE₁
  have hI := inverse_regular f x A h
  have hD := derivative_regular f x A h
  have assoc := multiply_associative G I D g i d hG hI hD
  have reciprocal := GaussianNameReciprocal.product_one G inverseClock g hG (inverse_input f x A h).andE₂
  have unit := cross_trans GI oneF oneF gi g d reciprocal (ones_equivalent g d)
  have cancel := multiply_cross GI oneF D D gi d d d
    (multiply_fast G I g i hG hI) (one_fast d) hD hD unit (cross_refl D d hD)
  exact cross_trans (multiplyF G (nameF f)) (multiplyF GI D) D _ _ d
    (cross_symm _ _ _ _ assoc) (cross_trans _ _ _ _ _ _ cancel (multiply_one_left D d hD))

theorem digamma_zero_of_derivative_zero (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hz : Γ ⊢[PRAAx] crossEquivalent (derivativeF f) zeroF (derivativeData x A) zero) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) zeroF (data f x A) zero := by
  let I := inverseF f
  let i := inverseData x A
  have hI := inverse_regular f x A h
  have move := multiply_cross I I (derivativeF f) zeroF i i (derivativeData x A) zero hI hI
    (derivative_regular f x A h) (zero_fast zero) (cross_refl I i hI) hz
  exact cross_trans _ _ _ _ _ _ move (GaussianNameRingLaws.multiply_zero_right I i zero zero)

theorem derivative_zero_of_digamma_zero (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hz : Γ ⊢[PRAAx] crossEquivalent (nameF f) zeroF (data f x A) zero) :
    Γ ⊢[PRAAx] crossEquivalent (derivativeF f) zeroF (derivativeData x A) zero := by
  let G := GaussianNamedGamma.nameF f
  let g := GaussianNamedGamma.data x A
  have hG := GaussianNamedGamma.name_regular f x A h.andE₁
  have move := multiply_cross G G (nameF f) zeroF g g (data f x A) zero hG hG
    (name_regular f x A h) (zero_fast zero) (cross_refl G g hG) hz
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (gamma_times_digamma f x A h))
    (cross_trans _ _ _ _ _ _ move (GaussianNameRingLaws.multiply_zero_right G g zero zero))

theorem zero_equivalent (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] Fm.iff (crossEquivalent (nameF f) zeroF (data f x A) zero)
        (crossEquivalent (derivativeF f) zeroF (derivativeData x A) zero) :=
  .iffI (.impI (derivative_zero_of_digamma_zero f x A h.wk Prf.hyp0))
    (.impI (digamma_zero_of_derivative_zero f x A h.wk Prf.hyp0))

theorem original_quotient_rate (f K : PR 2) (p x y A a : PTm n)
    (hr : Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples f x)
    (hs : Γ ⊢[PRAAx] GaussianNamedGammaEulerFirstDerivative.source f K p x y A a) : Γ ⊢[PRAAx]
    independentRate (GaussianNamedGammaEulerFirstDerivative.quotientF f K)
      (multiplyF (GaussianNamedGamma.nameF f) (nameF f))
      (GaussianNamedGammaEulerFirstDerivative.quotientData f K x y A a)
      (multiplyData (GaussianNamedGamma.nameF f) (nameF f) (GaussianNamedGamma.data x A) (data f x A))
      one (unit p) :=
  GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ one (unit p) (unit_positive p)
    (GaussianNamedGammaEulerFirstDerivative.original_first_derivative_rate f K p x y A a hs)
    (cross_refl _ _ (GaussianNamedGammaEulerFirstDerivative.quotient_regular f K p x y A a hs))
    (gamma_times_digamma f x A (.andI hs.andE₁ hr))

theorem actual_original_named_positive_digamma_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ pointCN (nameF f) (data f (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular f _ _ Prf.hyp0))

theorem actual_original_named_positive_digamma_zero_equivalent_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶
        Fm.iff (crossEquivalent (nameF f) zeroF (data f (var 0) (var 1)) zero)
          (crossEquivalent (derivativeF f) zeroF (derivativeData (var 0) (var 1)) zero)) :=
  closeUniv 2 (.impI (zero_equivalent f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveDigamma
