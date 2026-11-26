import IPRADerivations.Analysis.GaussianBarnesCanonicalDiskBound
import IPRADerivations.Analysis.GaussianCyclicExponentialSamples
import IPRADerivations.Analysis.GaussianNamedFiniteProductApartness

/-!
# Disk-uniform separation of the original Barnes prefactor

The two literal exponential factors are read at their original
multiplication clock. The exact inverse exponential lower bound for
each uses a common radius depending only on the admitted disk.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorUniformApartness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalDiskBound (prefactorRadius radius_le)
open GaussianBarnesCanonicalPrefactor (nameF data radius linearF linearData correctionF correctionData linear_input correction_input)
open GaussianCoefficientNameBounds (unit)
open GaussianCyclicExponentialSamples (sampleBound inverseBudget exponential_lower)
open GaussianNamedFiniteProductApartness (weaken_margin)
open GaussianNameReciprocal (lower apart anchor)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalLowerBounds (lower_congr product_lower)
open GaussianRadiusExponentialName (input)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentialDenominator (S : PTm n) : PTm n := two*sampleBound S
def denominator (R : PTm n) : PTm n :=
  exponentialDenominator (prefactorRadius R)*exponentialDenominator (prefactorRadius R)
def budget (R : PTm n) : PTm n := two*inverseBudget (prefactorRadius R)
def height (R : PTm n) : PTm n := GaussianRootSchedule.binaryLength (budget R+denominator R)

private theorem exponent_denominator_positive (S : PTm n) :
    Γ ⊢[PRAAx] le one (exponentialDenominator S) :=
  positive_product _ _ (le_succ_self one)
    (GaussianFactorBudget.power_positive (num 3) S (le_trans (le_succ_self one) (le_succ_self two)))

theorem denominator_positive (R : PTm n) : Γ ⊢[PRAAx] le one (denominator R) :=
  positive_product _ _ (exponent_denominator_positive (prefactorRadius R)) (exponent_denominator_positive (prefactorRadius R))

private theorem exponential_lower_at_radius (f : PR 2) (r S x p : PTm n)
    (hf : Γ ⊢[PRAAx] input f r x) (hr : Γ ⊢[PRAAx] le r S) (hp : Γ ⊢[PRAAx] le (two*inverseBudget S) (unit p)) :
    Γ ⊢[PRAAx] lower (ap2 (GaussianRadiusExponentialName.nameF f) p (GaussianRadiusExponentialName.data r x))
      (exponentialDenominator S) := by
  have bound : Γ ⊢[PRAAx] le (sampleBound r) (sampleBound S) :=
    GaussianFactorBudget.power_monotone_length (num 3) r S (le_trans (le_succ_self one) (le_succ_self two)) hr
  have cost : Γ ⊢[PRAAx] le (inverseBudget r) (inverseBudget S) :=
    add_le_add_right two (le_mul_mono (le_refl (num 4)) bound)
  have native := exponential_lower f r x p hf (le_trans (le_mul_mono (le_refl two) cost) hp)
  exact weaken_margin _ _ _ (exponent_denominator_positive r) (le_mul_mono (le_refl two) bound) native

theorem sample_lower (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hp : Γ ⊢[PRAAx] le (budget R) (unit p)) :
    Γ ⊢[PRAAx] lower (ap2 nameF p (data z B)) (denominator R) := by
  let r := radius z B
  let S := prefactorRadius R
  let f := GaussianRadiusExponentialName.nameF linearF
  let g := GaussianRadiusExponentialName.nameF correctionF
  let x := GaussianRadiusExponentialName.data r (linearData z B)
  let y := GaussianRadiusExponentialName.data r (correctionData z B)
  let t := productClock f g x y p
  have ht : Γ ⊢[PRAAx] le (budget R) (unit t) :=
    le_trans hp (GaussianBalancedRadiusArithmetic.unit_monotone p t (le_add_right _ _))
  have radiusBound := radius_le z R B h
  have left := exponential_lower_at_radius linearF r S (linearData z B) t (linear_input z B) radiusBound ht
  have right := exponential_lower_at_radius correctionF r S (correctionData z B) t (correction_input z B) radiusBound ht
  have hd := exponent_denominator_positive (Γ := Γ) S
  exact lower_congr (product_at f g x y p).eqSymm (one_mul one) (.eqRefl _)
    (product_lower (ap2 f t x) (ap2 g t y) one (exponentialDenominator S) one (exponentialDenominator S) hd hd left right)

theorem original_apart (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] apart nameF (height R) (data z B) := by
  let H := height R
  let p := anchor H
  have pay : Γ ⊢[PRAAx] le (budget R+denominator R) (unit H) :=
    (GaussianRootSchedule.binary_length_correct _).andE₁
  have hp : Γ ⊢[PRAAx] le (budget R) (unit p) :=
    le_trans (le_add_right _ _) (le_trans pay (GaussianBalancedRadiusArithmetic.unit_monotone H p (le_add_right _ _)))
  exact weaken_margin _ _ _ (denominator_positive R) (le_trans (le_add_left _ _) pay) (sample_lower p z R B h hp)

theorem actual_Barnes_prefactor_disk_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ apart nameF (height (var 1)) (data (var 0) (var 2))) :=
  closeUniv 3 (.impI (original_apart _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorUniformApartness
