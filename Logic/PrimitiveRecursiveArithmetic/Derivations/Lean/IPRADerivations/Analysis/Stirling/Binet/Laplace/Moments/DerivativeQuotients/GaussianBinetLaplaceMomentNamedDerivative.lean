import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.Named.GaussianBinetLaplaceMomentNamedShift
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# Two-sided derivatives of the original named Binet moments

Freeze the actual base, translated inputs, and successor on the same
rational base observation. The original quotient programs inherit the
fixed-margin rational Taylor error. The comparison clock pays for
both endpoint perturbations after division by the actual step.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNamedDerivative

open_ipra
open GaussianBinetLaplaceMomentBackwardWindow (lowerData lowerNumerator)
open GaussianBinetLaplaceMomentForwardMargin (upperRadius)
open GaussianBinetLaplaceMomentNamed (clock clock_margin frozen_rate name_regular)
open GaussianBinetLaplaceMomentNamedShift (source negativeStep translated_sources frozen_source shifted_charts)
open GaussianBinetLaplaceMomentImproper (regular)
open GaussianBinetLaplaceMomentTwoSidedMargin (lower_source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusNumerator)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianNamedGammaIncrementInput (incrementF incrementData clock_later)
open GaussianNamedRightHalfPlane (threshold)
open GaussianNamedRightHalfPlaneSigned (realNumerator denominator)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk Γ t)
local notation "N" => GaussianBinetLaplaceMomentNamed.nameF
local notation "nd" => GaussianBinetLaplaceMomentNamed.data
local notation "J" => GaussianBinetLaplaceMomentImproper.nameF
local notation "jd" => GaussianBinetLaplaceMomentImproper.data
local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data
local notation "shiftClock" => GaussianNamedGammaIncrementInput.clock
local notation "Fbudget" => GaussianBinetLaplaceMomentForwardMargin.linearBudget
local notation "Bbudget" => GaussianBinetLaplaceMomentTwoSidedMargin.backwardBudget
local notation "Kf" => GaussianBinetLaplaceMomentForwardQuotient.quotientF
local notation "Tf" => GaussianBinetLaplaceMomentForwardQuotient.targetF

def forwardF (f : PR 2) : PR 2 := QF (N (incrementF f)) (N f)
def backwardF (f : PR 2) : PR 2 := QF (N f) (N (incrementF f))
def targetF (f : PR 2) : PR 2 := negativeF (N f)

def forwardData (f : PR 2) (x M j H Q : PTm n) : PTm n :=
  qd (N (incrementF f)) (N f) (nd (incrementData x (radiusNumerator H) Q) (two*M) j) (nd x M j) (radiusNumerator H) Q

def backwardData (f : PR 2) (x M j H Q : PTm n) : PTm n :=
  qd (N f) (N (incrementF f)) (nd x M j) (nd (incrementData x (negativeStep H) Q) (two*M) j) (radiusNumerator H) Q

def targetData (x M j : PTm n) : PTm n := negativeData (nd x M (succ j))

def forwardBudget (j M H : PTm n) : PTm n := Fbudget j (two*M) H+H
def backwardBudget (j M H : PTm n) : PTm n := Bbudget j (two*M) H+H

def comparisonPrecision (Q : PTm n) : PTm n := exponent ((two*Q+one)*Q) zero
def frozenClock (s M j : PTm n) : PTm n := clock s (two*M) j + clock s M j + clock s M (succ j)

theorem comparison_budget (Q : PTm n) : Γ ⊢[PRAAx] le ((two*Q+one)*Q) (unit (comparisonPrecision Q)) :=
  le_congr ((congrMul (.eqRefl _) (pw_zero two)).eqTrans (by ipra_ring)) (.eqRefl _)
    (query_budget ((two*Q+one)*Q) zero)

private theorem quotient_frozen_rate (F G : PR 2) (x y u v h Q S : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated h Q) (hS : Γ ⊢[PRAAx] le one S)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (hu : Γ ⊢[PRAAx] pointCN J u) (hv : Γ ⊢[PRAAx] pointCN J v)
    (hl : Γ ⊢[PRAAx] independentRate F J x u one S) (hr : Γ ⊢[PRAAx] independentRate G J y v one S) :
    Γ ⊢[PRAAx] independentRate (QF F G) Kf (qd F G x y h Q) (qd J J u v h Q) (two*Q) S := by
  let A := GaussianNamedDifferenceRate.leadingNumerator one S one S
  let D := GaussianNamedDifferenceRate.leadingDenominator S S
  have hD : Γ ⊢[PRAAx] le one D := positive_product S S hS hS
  have raw := GaussianNamedDifferenceQuotientRate.quotient_rate F G J J x y u v h Q one S one S hs
    (.andI (.andI hS hS) (.andI (.andI hf hg) (.andI (.andI hu hv) (.andI hl hr))))
  exact GaussianNamedRateRadius.weaken _ _ _ _ (Q*A) D (two*Q) S hD hS
    (le_of_eq_add (d := zero) (by
      dsimp only [A,D,GaussianNamedDifferenceRate.leadingNumerator,GaussianNamedDifferenceRate.leadingDenominator]
      ipra_ring)) raw

private theorem join (F G : PR 2) (x y u v A H Q : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hQ : Γ ⊢[PRAAx] le one Q)
    (hf : Γ ⊢[PRAAx] independentRate F Kf x u (two*Q) (unit (comparisonPrecision Q)))
    (hr : Γ ⊢[PRAAx] independentRate Kf Tf u v A Q)
    (hg : Γ ⊢[PRAAx] independentRate Tf G v y one (unit (comparisonPrecision Q))) :
    Γ ⊢[PRAAx] independentRate F G x y (A+H) Q := by
  let S := unit (comparisonPrecision Q)
  let B := GaussianNamedRateComposition.leadingNumerator (two*Q) S A Q
  let D := GaussianNamedRateComposition.leadingDenominator S Q
  let C := GaussianNamedRateComposition.leadingNumerator B D one S
  let E := GaussianNamedRateComposition.leadingDenominator D S
  have hS : Γ ⊢[PRAAx] le one S := unit_positive _
  have hD : Γ ⊢[PRAAx] le one D := positive_product S Q hS hQ
  have hE : Γ ⊢[PRAAx] le one E := positive_product D S hD hS
  have first := GaussianNamedRateComposition.compose F Kf Tf x u v (two*Q) S A Q hS hQ hf hr
  have rest := GaussianNamedRateComposition.compose F Tf G x v y B D one S hD hS first hg
  apply GaussianNamedRateRadius.weaken F G x y C E (A+H) Q hE hQ ?_ rest
  have room : Γ ⊢[PRAAx] le ((two*Q+one)*Q) S := comparison_budget Q
  dsimp only [C,E,B,D,GaussianNamedRateComposition.leadingNumerator,GaussianNamedRateComposition.leadingDenominator]
  ipra_le 𝔞(Q)*𝔞(S)*sl room+𝔞(Q)*𝔞(S)^2*sl hH

theorem two_sided_rate (f : PR 2) (x M j H Q : PTm n) (h : Γ ⊢[PRAAx] source f x M H Q) :
    Γ ⊢[PRAAx] independentRate (forwardF f) (targetF f) (forwardData f x M j H Q) (targetData x M j)
        (forwardBudget j M H) Q ⋏
      independentRate (backwardF f) (targetF f) (backwardData f x M j H Q) (targetData x M j)
        (backwardBudget j M H) Q := by
  let s := comparisonPrecision Q
  let S := unit s
  let m := two*M
  let k := frozenClock s M j
  let t := shiftClock k
  let q := ap2 f t x
  let X := realNumerator q
  let D := denominator q
  let R := radius X zero
  let a := incrementData x (radiusNumerator H) Q
  let b := incrementData x (negativeStep H) Q
  let G := incrementF f
  let d := nd x M j
  let u := nd a m j
  let v := nd b m j
  let f₀ := jd j X D R
  let f₁ := jd (succ j) X D R
  let fPlus := jd j (X*Q+H*D) (D*Q) (upperRadius X D H Q)
  let fMinus := lowerData j X D H Q
  have hH := h.andE₂.andE₁
  have hQ := h.andE₂.andE₂.andE₁
  have hS : Γ ⊢[PRAAx] le one S := unit_positive s
  have hp : Γ ⊢[PRAAx] le (clock s m j) k :=
    le_trans (le_add_right _ (clock s M j)) (le_add_right _ _)
  have h₀ : Γ ⊢[PRAAx] le (clock s M j) t :=
    le_trans (le_trans (le_add_left _ (clock s m j)) (le_add_right _ (clock s M (succ j)))) (clock_later k)
  have h₁ : Γ ⊢[PRAAx] le (clock s M (succ j)) t :=
    le_trans (le_add_left _ (clock s m j+clock s M j)) (clock_later k)
  have hm := le_trans (clock_margin s M j) h₀
  have hk := le_trans (clock_margin s m j) hp
  have hr := frozen_source f t x M H Q h hm
  have hs := translated_sources f x M H Q h
  have ht := shifted_charts f k x M j H Q h hk hm
  have hu := GaussianBinetLaplaceMomentForwardMargin.upper_source X D R H Q hr.andE₁ hQ
  have hl := lower_source X D R m H Q hr
  have rc := name_regular f x M j h.andE₁
  have ra := name_regular G a m j hs.andE₁
  have rb := name_regular G b m j hs.andE₂
  have r₀ := regular j X D R hr.andE₁
  have rPlus := regular j (X*Q+H*D) (D*Q) (upperRadius X D H Q) hu
  have rMinus := regular j (lowerNumerator X D H Q) (D*Q) (radius (lowerNumerator X D H Q) zero) hl
  have fr₀ : Γ ⊢[PRAAx] independentRate (N f) J d f₀ one S := frozen_rate f s t x M j h.andE₁ h₀
  have fr₁ : Γ ⊢[PRAAx] independentRate (N f) J (nd x M (succ j)) f₁ one S :=
    frozen_rate f s t x M (succ j) h.andE₁ h₁
  have frPlus : Γ ⊢[PRAAx] independentRate (N G) J u fPlus one S :=
    GaussianNamedRateTransport.transport (N G) J (N G) J u (GaussianBinetLaplaceMomentNamed.frozenData G k a j)
      u fPlus one S hS (frozen_rate G s k a m j hs.andE₁ hp) (cross_refl (N G) u ra)
      (cross_symm _ _ _ _ ht.andE₁)
  have frMinus : Γ ⊢[PRAAx] independentRate (N G) J v fMinus one S :=
    GaussianNamedRateTransport.transport (N G) J (N G) J v (GaussianBinetLaplaceMomentNamed.frozenData G k b j)
      v fMinus one S hS (frozen_rate G s k b m j hs.andE₂ hp) (cross_refl (N G) v rb)
      (cross_symm _ _ _ _ ht.andE₂)
  have param := GaussianBinetLaplaceMomentForwardQuotient.positive_parameter H Q hH hQ
  have plus := quotient_frozen_rate (N G) (N f) u d fPlus f₀ (radiusNumerator H) Q S param hS ra rc rPlus r₀ frPlus fr₀
  have minus := quotient_frozen_rate (N f) (N G) d v f₀ fMinus (radiusNumerator H) Q S param hS rc rb r₀ rMinus fr₀ frMinus
  have tr := GaussianEulerPowerScalingCompactRate.negative_rate (N f) J (nd x M (succ j)) f₁ one S
    (name_regular f x M (succ j) h.andE₁) (regular (succ j) X D R hr.andE₁) hS fr₁
  have target := GaussianNamedRateComposition.symmetric (targetF f) Tf (targetData x M j)
    (GaussianBinetLaplaceMomentForwardQuotient.targetData j X D R) one S hS tr
  have rational := GaussianBinetLaplaceMomentTwoSidedMargin.two_sided_rate j X D R m H Q hr
  exact .andI
    (join (forwardF f) (targetF f) (forwardData f x M j H Q) (targetData x M j) _ _ (Fbudget j m H) H Q
      hH hQ plus rational.andE₁ target)
    (join (backwardF f) (targetF f) (backwardData f x M j H Q) (targetData x M j) _ _ (Bbudget j m H) H Q
      hH hQ minus rational.andE₂ target)

theorem actual_original_named_Binet_moment_two_sided_derivative_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let x := var 0
       let M := var 1
       let j := var 2
       let H := var 3
       let Q := var 4
       source f x M H Q ⟶
         (independentRate (forwardF f) (targetF f) (forwardData f x M j H Q) (targetData x M j)
           (forwardBudget j M H) Q ⋏
         independentRate (backwardF f) (targetF f) (backwardData f x M j H Q) (targetData x M j)
           (backwardBudget j M H) Q)) :=
  closeUniv 5 (.impI (two_sided_rate f _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNamedDerivative
