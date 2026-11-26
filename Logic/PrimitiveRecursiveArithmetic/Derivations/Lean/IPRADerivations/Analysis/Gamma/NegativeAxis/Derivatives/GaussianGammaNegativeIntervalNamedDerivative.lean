import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalNamedGamma
import IPRADerivations.Analysis.Gamma.Digamma.NegativeAxis.GaussianGammaNegativeIntervalNamedDigamma
import IPRADerivations.Analysis.Gamma.Digamma.NegativeAxis.GaussianGammaNegativeIntervalDigammaRate

/-!
# Original unscaled Gamma quotients at named negative offsets

The product of the named Gamma and shifted digamma is the common
limit of the original unscaled forward unit-step quotients with
sufficiently late rational offsets and sufficiently small steps.
The offset clock is uniform across its rational encodings. The
step cutoff is explicit for each encoding.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaNegativeCriticalSlope (coefficient)
open GaussianGammaNegativeIntervalNamedGamma (actualF actualData actual_regular actual_frozen_rate rateFactor)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator frozen_guard)
open GaussianGammaNegativeIntervalNamedLog (clock)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameRingLaws (three)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (same_denominator symmetric)
open GaussianNamedRateRadius (weaken)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaNegativeIntervalNamedDigamma.nameF
local notation "dd" => GaussianGammaNegativeIntervalNamedDigamma.data
local notation "NF" => GaussianGammaNegativeCriticalEndpoints.nameF
local notation "nd" => GaussianGammaNegativeCriticalEndpoints.nameData
local notation "gd" => GaussianGammaNegativeIntervalNative.data
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "qd" => GaussianGammaNegativeIntervalStep.data
local notation "TF" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "td" => GaussianGammaNegativeIntervalDerivativeTarget.data
local notation "cost" => GaussianGammaNegativeIntervalDerivativeRate.cost
local notation "minimumDenominator" => GaussianGammaNegativeIntervalDigammaRate.minimumDenominator

def nameF (f : PR 2) : PR 2 := multiplyF (actualF f) (DF f)
def data (f : PR 2) (x E N : PTm n) : PTm n := multiplyData (actualF f) (DF f) (actualData f x E N) (dd x E N)

def precision (f : PR 2) (p x E N : PTm n) : PTm n := exponent (rateFactor f x E N) p + exponent (coefficient N E) p
def freezeClock (f : PR 2) (p x E N : PTm n) : PTm n :=
  clock (precision f p x E N) E N + precision f p x E N

def minimumStep (f : PR 2) (p k x N : PTm n) : PTm n :=
  let a := sampleNumerator f k x
  let b := sampleDenominator f k x
  minimumDenominator (exponent (cost a b N) p) a b

def productCost (f : PR 2) (x E N : PTm n) : PTm n :=
  U (DF f) (dd x E N)+(U (actualF f) (actualData f x E N)+three)

theorem name_regular (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f x E N) :=
  multiply_fast _ _ _ _ (actual_regular f x E N hs) (GaussianGammaNegativeIntervalNamedDigamma.name_regular f x E N hs)

private theorem unit_leading (F G : PR 2) (x y A p s : PTm n) (late : Γ ⊢[PRAAx] le (exponent A p) s)
    (h : Γ ⊢[PRAAx] independentRate F G x y A (unit s)) :
    Γ ⊢[PRAAx] independentRate F G x y one (unit p) := by
  exact weaken F G x y A (unit s) one (unit p) (unit_positive s) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (le_trans (query_budget A p) (unit_monotone late))) h

theorem frozen_product_rate (f : PR 2) (p k x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E)
    (hk : Γ ⊢[PRAAx] le (freezeClock f p x E N) k) : Γ ⊢[PRAAx]
    independentRate (nameF f) TF (data f x E N) (td (sampleNumerator f k x) (sampleDenominator f k x) N)
      (productCost f x E N) (unit p) := by
  let r := precision f p x E N
  let a := sampleNumerator f k x
  let b := sampleDenominator f k x
  let X := actualData f x E N
  let Y := dd x E N
  let Z := gd a b N
  let W := nd a b N
  let M := U (DF f) Y
  let R := U (actualF f) X+three
  have base := frozen_guard f k x E hs
  have hX := actual_regular f x E N hs
  have hY := GaussianGammaNegativeIntervalNamedDigamma.name_regular f x E N hs
  have hZ := GaussianGammaNegativeIntervalNative.negative_regular a b N base
  have hW := GaussianGammaNegativeCriticalEndpoints.name_regular a b N base
  have hc : Γ ⊢[PRAAx] le (clock r E N) k := le_trans (le_add_right _ _) hk
  have hr : Γ ⊢[PRAAx] le r k := le_trans (le_add_left _ _) hk
  have gamma := unit_leading (actualF f) gammaF X Z (rateFactor f x E N) p r
    (le_add_right _ _) (actual_frozen_rate f r k x E N hs hc)
  have digamma := unit_leading (DF f) NF Y W (coefficient N E) p k (le_trans (le_add_left _ _) hr)
    (GaussianGammaNegativeIntervalNamedDigamma.original_frozen_rate f k x E N hs)
  have bound : Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound gammaF Z R :=
    (GaussianGammaNegativeIntervalExponentialFreeze.second_input (actualF f) gammaF X Z p hX hZ gamma).andE₂
  have hp := unit_positive (Γ := Γ) p
  have product := GaussianNamedMultiplyRate.independent_rate (actualF f) (DF f) gammaF NF X Y Z W
    one (unit p) one (unit p) M R hp hp hX hY hZ hW (all_samples_bounded _ _ hY) bound gamma digamma
  exact weaken (nameF f) TF (data f x E N) (td a b N) _ _ (productCost f x E N) (unit p)
    (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := LeanProofs.ConciseIPRA.PTm.zero) (by
      dsimp only [GaussianNamedMultiplyRate.leadingNumerator,GaussianNamedMultiplyRate.leadingDenominator,productCost,M,R,Y,X]
      ipra_ring)) product

theorem original_rate (f : PR 2) (p k x E N D : PTm n) (hs : Γ ⊢[PRAAx] source f x E)
    (hk : Γ ⊢[PRAAx] le (freezeClock f p x E N) k) (hD : Γ ⊢[PRAAx] le (minimumStep f p k x N) D) : Γ ⊢[PRAAx]
    independentRate QF (nameF f) (qd (sampleNumerator f k x) (sampleDenominator f k x) N D) (data f x E N)
      (one+productCost f x E N) (unit p) := by
  let a := sampleNumerator f k x
  let b := sampleDenominator f k x
  let r := exponent (cost a b N) p
  have raw := GaussianGammaNegativeIntervalDigammaRate.original_derivative_rate r a b N D (frozen_guard f k x E hs) hD
  have small := unit_leading QF TF (qd a b N D) (td a b N) (cost a b N) p r (le_refl r) raw
  have hp := unit_positive (Γ := Γ) p
  exact same_denominator QF TF (nameF f) (qd a b N D) (td a b N) (data f x E N) one (unit p)
    (productCost f x E N) hp small
    (symmetric (nameF f) TF (data f x E N) (td a b N) (productCost f x E N) (unit p) hp
      (frozen_product_rate f p k x E N hs hk))

theorem actual_original_negative_interval_named_Gamma_quotient_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((source f (var 0) (var 1) ⋏ (le (freezeClock f (var 3) (var 0) (var 1) (var 2)) (var 4) ⋏
        le (minimumStep f (var 3) (var 4) (var 0) (var 2)) (var 5))) ⟶
        independentRate QF (nameF f)
          (qd (sampleNumerator f (var 4) (var 0)) (sampleDenominator f (var 4) (var 0)) (var 2) (var 5))
          (data f (var 0) (var 1) (var 2)) (one+productCost f (var 0) (var 1) (var 2)) (unit (var 3))) :=
  closeUniv 6 (.impI (original_rate f _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedDerivative
