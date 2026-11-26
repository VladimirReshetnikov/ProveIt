import IPRADerivations.Analysis.Gamma.Names.Continuation.GaussianNamedGammaBackwardIdentification
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaFirstCrossing
import IPRADerivations.Analysis.Names.GoldenRatio.GaussianNamedGoldenRatioProduct

/-!
# The second Gamma crossing reduces to a named product

At a certified positive real name z with z−1 apart from zero, multiply
the crossing by the actual name z−1. The backward and forward Gamma
recurrences identify the products with Gamma(z) and z(z−1) Gamma(z).
Explicit reciprocal certificates justify cancellation in both directions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaSecondCrossingProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedGammaBackwardShift (minusOneF minusOneData)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianNamedGoldenRatioProduct (equation productF productData)
open GaussianNamedGammaFirstCrossing (cancel_right positive_gamma_apart inverseClock)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (oneF one_fast multiply_one_left multiply_associative multiply_commutative)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianRationalReciprocal (qone)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (f : PR 2) (x A a : PTm n) : Fm PTm n :=
  GaussianNamedGammaBackwardShift.source f x A a ⋏ realSamples f x

abbrev lowerF (f : PR 2) : PR 2 := GaussianNamedGammaBackwardShift.nameF f
abbrev upperF (f : PR 2) : PR 2 := GaussianNamedGamma.nameF (shiftF f)
def lowerData (f : PR 2) (x A a : PTm n) : PTm n := GaussianNamedGammaBackwardShift.data f x A a
def upperData (x A : PTm n) : PTm n := GaussianNamedGamma.data (shiftData x) A

def crossing (f : PR 2) (x A a : PTm n) : Fm PTm n :=
  crossEquivalent (lowerF f) (upperF f) (lowerData f x A a) (upperData x A)

private theorem one_constant (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent oneF constantF x qone :=
  cross_trans _ _ _ _ _ _ (GaussianBoundedInverseApartness.ones_equivalent x zero)
    GaussianGammaEncodingRescaling.one_constant_cross

theorem gamma_plus_regular (f : PR 2) (x A : PTm n) (hs : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A) :
    Γ ⊢[PRAAx] pointCN (upperF f) (upperData x A) :=
  GaussianNamedGamma.name_regular _ _ _ (GaussianEulerNamedShiftInput.original_source f x A hs)

theorem weighted_upper (f : PR 2) (x A : PTm n) (hs : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x A) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (minusOneF f) (upperF f)) (multiplyF (productF f) (GaussianNamedGamma.nameF f))
      (multiplyData (minusOneF f) (upperF f) (minusOneData x) (upperData x A))
      (multiplyData (productF f) (GaussianNamedGamma.nameF f) (productData f x) (GaussianNamedGamma.data x A)) := by
  let W := minusOneF f
  let G := GaussianNamedGamma.nameF f
  let w := minusOneData x
  let g := GaussianNamedGamma.data x A
  let L := upperF f
  let l := upperData x A
  let P := productF f
  let v := productData f x
  let K := multiplyF f G
  let k := multiplyData f G x g
  let C := multiplyF W f
  let c := multiplyData W f w x
  have hf := hs.andE₁
  have hw := GaussianNamedGammaBackwardShift.minus_one_regular f x hf
  have hg := GaussianNamedGamma.name_regular f x A hs
  have hl := gamma_plus_regular f x A hs
  have hp : Γ ⊢[PRAAx] pointCN P v := multiply_fast f W x w hf hw
  have hc := multiply_fast W f w x hw hf
  have compare := GaussianEulerNamedIBPRecurrence.original_named_Gamma_IBP_recurrence f x A hs
  have lift := multiply_cross W W L K w w l k hw hw hl (multiply_fast f G x g hf hg) (cross_refl W w hw) compare
  have assoc := multiply_associative W f G w x g hw hf hg
  have swap := multiply_cross C P G G c v g g hc hp hg hg
    (multiply_commutative W f w x hw hf) (cross_refl G g hg)
  exact cross_trans (multiplyF W L) (multiplyF W K) (multiplyF P G)
    (multiplyData W L w l) (multiplyData W K w k) (multiplyData P G v g) lift
    (cross_trans (multiplyF W K) (multiplyF C G) (multiplyF P G) _ _ _
      (cross_symm (multiplyF C G) (multiplyF W K) _ _ assoc) swap)

theorem crossing_implies_product (f : PR 2) (x A a : PTm n)
    (hs : Γ ⊢[PRAAx] source f x A a) (he : Γ ⊢[PRAAx] crossing f x A a) :
    Γ ⊢[PRAAx] equation f x := by
  let W := minusOneF f
  let w := minusOneData x
  let E := lowerF f
  let e := lowerData f x A a
  let L := upperF f
  let l := upperData x A
  let G := GaussianNamedGamma.nameF f
  let g := GaussianNamedGamma.data x A
  let P := productF f
  let v := productData f x
  have hf := hs.andE₁.andE₁.andE₁
  have hw := GaussianNamedGammaBackwardShift.minus_one_regular f x hf
  have hg := GaussianNamedGamma.name_regular f x A hs.andE₁.andE₁
  have hl := gamma_plus_regular f x A hs.andE₁.andE₁
  have he' := GaussianNamedGammaBackwardShift.name_regular f x A a hs.andE₁
  have hP : Γ ⊢[PRAAx] pointCN P v := multiply_fast f W x w hf hw
  have lift := multiply_cross W W L E w w l e hw hw hl he' (cross_refl W w hw)
    (cross_symm E L e l he)
  have recurrence := GaussianNamedGammaBackwardShift.shifted_product f x A a hs.andE₁
  have upper := weighted_upper f x A hs.andE₁.andE₁
  have bare : Γ ⊢[PRAAx] crossEquivalent (multiplyF P G) G (multiplyData P G v g) g :=
    cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ upper) (cross_trans _ _ _ _ _ _ lift recurrence)
  have asOne := cross_trans _ _ _ _ _ _ bare (cross_symm _ _ _ _ (multiply_one_left G g hg))
  have apart := positive_gamma_apart f x A (.andI hs.andE₁.andE₁ hs.andE₂)
  have result := cancel_right P oneF G v g g inverseClock hP (one_fast g) hg apart asOne
  exact cross_trans P oneF constantF v g qone result (one_constant g)

theorem product_implies_crossing (f : PR 2) (x A a : PTm n)
    (hs : Γ ⊢[PRAAx] source f x A a) (he : Γ ⊢[PRAAx] equation f x) :
    Γ ⊢[PRAAx] crossing f x A a := by
  let W := minusOneF f
  let w := minusOneData x
  let E := lowerF f
  let e := lowerData f x A a
  let L := upperF f
  let l := upperData x A
  let G := GaussianNamedGamma.nameF f
  let g := GaussianNamedGamma.data x A
  let P := productF f
  let v := productData f x
  have hf := hs.andE₁.andE₁.andE₁
  have hw := GaussianNamedGammaBackwardShift.minus_one_regular f x hf
  have hg := GaussianNamedGamma.name_regular f x A hs.andE₁.andE₁
  have hl := gamma_plus_regular f x A hs.andE₁.andE₁
  have he' := GaussianNamedGammaBackwardShift.name_regular f x A a hs.andE₁
  have hp : Γ ⊢[PRAAx] pointCN P v := multiply_fast f W x w hf hw
  have coeff := cross_trans P constantF oneF v qone g he (cross_symm _ _ _ _ (one_constant g))
  have moved := multiply_cross P oneF G G v g g g hp (one_fast g) hg hg coeff (cross_refl G g hg)
  have recur := GaussianNamedGammaBackwardShift.shifted_product f x A a hs.andE₁
  have upper := weighted_upper f x A hs.andE₁.andE₁
  have upper_to_g := cross_trans _ _ _ _ _ _ upper (cross_trans _ _ _ _ _ _ moved (multiply_one_left G g hg))
  have commuteL := multiply_commutative W L w l hw hl
  have commuteE := multiply_commutative E W e w he' hw
  have joined : Γ ⊢[PRAAx] crossEquivalent (multiplyF E W) (multiplyF L W)
      (multiplyData E W e w) (multiplyData L W l w) :=
    cross_trans _ _ _ _ _ _ commuteE
      (cross_trans _ _ _ _ _ _ recur (cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ commuteL) upper_to_g)))
  exact cancel_right E L W e l w a he' hl hw hs.andE₁.andE₂ joined

theorem actual_original_named_Gamma_second_crossing_product_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ Fm.iff (crossing f (var 0) (var 1) (var 2)) (equation f (var 0))) :=
  closeUniv 3 (.impI (.andI (.impI (crossing_implies_product f _ _ _ Prf.hyp1 Prf.hyp0))
    (.impI (product_implies_crossing f _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaSecondCrossingProduct
