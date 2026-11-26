import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.GaussianNamedEulerLogarithmicNamedDerivative
import IPRADerivations.Analysis.Euler.Logarithms.GaussianNamedEulerLogarithmicZeroIdentification
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedIncrementDifferenceQuotientProperness
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# The first Euler derivative of the actual named Gamma evaluator

Order-zero identification at both original input names carries the
logarithmic derivative to the quotient made directly from the actual
named Gamma programs. The reciprocal of the certified increment is
the same evaluator in both quotients.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaEulerFirstDerivative

open_ipra
open GaussianNamedGammaSmallIncrementInput (sumData)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "gF" => GaussianNamedGamma.nameF
local notation "gData" => GaussianNamedGamma.data
local notation "iF" => GaussianNamedEulerLogarithmicImproper.nameF
local notation "iData" => GaussianNamedEulerLogarithmicImproper.data
local notation "sumF" => GaussianNamedGammaSmallIncrementInput.sumF
local notation "QF" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "QD" => GaussianNamedIncrementDifferenceQuotient.data

abbrev source (f K : PR 2) (p x y A a : PTm n) : Fm PTm n :=
  GaussianNamedEulerLogarithmicNamedDerivative.source f K p zero x y A a
def quotientF (f K : PR 2) : PR 2 := QF (gF (sumF f K)) (gF f) K
def quotientData (f K : PR 2) (x y A a : PTm n) : PTm n :=
  QD (gF (sumF f K)) (gF f) K (gData (sumData x y) (two*A)) (gData x A) y a

ipra_subst quotientData

theorem original_quotient_proper (f K : PR 2) (p x y A a : PTm n) (hs : Γ ⊢[PRAAx] source f K p x y A a) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedEulerLogarithmicNamedDerivative.quotientF f K) (quotientF f K)
      (GaussianNamedEulerLogarithmicNamedDerivative.quotientData f K zero x y A a) (quotientData f K x y A a) := by
  let f' := sumF f K
  let x' := sumData x y
  let A' := two*A
  have base := hs.andE₁
  have moved := GaussianNamedEulerLogarithmicNamedDerivative.shifted_name_source f K p zero x y A a hs
  have iLeft := GaussianNamedEulerLogarithmicImproper.name_regular f' zero x' A' moved
  have iRight := GaussianNamedEulerLogarithmicImproper.name_regular f zero x A base
  have gLeft := GaussianNamedGamma.name_regular f' x' A' moved
  have gRight := GaussianNamedGamma.name_regular f x A base
  exact GaussianNamedIncrementDifferenceQuotientProperness.proper (iF f') (gF f') (iF f) (gF f) K
    (iData zero x' A') (gData x' A') (iData zero x A) (gData x A) y a
    iLeft gLeft iRight gRight hs.andE₂.andE₁
    (GaussianNamedEulerLogarithmicZeroIdentification.original_order_zero_is_Gamma f' x' A' moved)
    (GaussianNamedEulerLogarithmicZeroIdentification.original_order_zero_is_Gamma f x A base)

theorem quotient_regular (f K : PR 2) (p x y A a : PTm n) (hs : Γ ⊢[PRAAx] source f K p x y A a) :
    Γ ⊢[PRAAx] pointCN (quotientF f K) (quotientData f K x y A a) := by
  have moved := GaussianNamedEulerLogarithmicNamedDerivative.shifted_name_source f K p zero x y A a hs
  exact GaussianNamedIncrementDifferenceQuotient.name_regular _ _ _ _ _ _ _
    (.andI (GaussianNamedGamma.name_regular _ _ _ moved)
      (.andI (GaussianNamedGamma.name_regular f x A hs.andE₁) hs.andE₂.andE₁))

theorem original_first_derivative_rate (f K : PR 2) (p x y A a : PTm n) (hs : Γ ⊢[PRAAx] source f K p x y A a) :
    Γ ⊢[PRAAx] independentRate (quotientF f K) (iF f) (quotientData f K x y A a) (iData one x A) one (unit p) :=
  GaussianNamedRateTransport.transport (GaussianNamedEulerLogarithmicNamedDerivative.quotientF f K) (iF f)
    (quotientF f K) (iF f) _ _ _ _ one (unit p) (unit_positive p)
    (GaussianNamedEulerLogarithmicNamedDerivative.original_derivative_rate f K p zero x y A a hs)
    (cross_symm _ _ _ _ (original_quotient_proper f K p x y A a hs))
    (cross_refl (iF f) (iData one x A) (GaussianNamedEulerLogarithmicImproper.name_regular f one x A hs.andE₁))

theorem original_observations (f K : PR 2) (q v p x y A a : PTm n) (hs : Γ ⊢[PRAAx] source f K p x y A a) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (quotientF f K) q (quotientData f K x y A a)) (ap2 (iF f) v (iData one x A))
      (rateNumerator one (unit p) q v) (rateDenominator (unit p) q v) :=
  rate_at (quotientF f K) (iF f) _ _ _ _ q v (original_first_derivative_rate f K p x y A a hs)

theorem actual_original_named_Gamma_first_Euler_derivative_closed (f K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source f K (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      independentRate (quotientF f K) (iF f) (quotientData f K (var 1) (var 2) (var 3) (var 4))
        (iData one (var 1) (var 3)) one (unit (var 0))) :=
  closeUniv 5 (.impI (original_first_derivative_rate f K _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaEulerFirstDerivative
