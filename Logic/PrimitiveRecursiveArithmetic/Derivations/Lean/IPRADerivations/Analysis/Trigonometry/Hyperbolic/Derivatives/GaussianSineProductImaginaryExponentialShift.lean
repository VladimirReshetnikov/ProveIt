import IPRADerivations.Analysis.Exponential.Names.Derivatives.GaussianNamedExponentialShiftDerivative
import IPRADerivations.Analysis.Trigonometry.Pi.GaussianPiRationalScaleRepresentation
import IPRADerivations.Analysis.Trigonometry.Hyperbolic.GaussianSineProductImaginaryHyperbolic

/-!
# First-order rates for the two exponential names in hyperbolic sine

The base input retains its original rational representation. The later
input uses a positive common rescaling and one numerator unit, producing
the exact increment (1/(kB)). The error coefficient depends on the
original base and the original π name.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryExponentialShift

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNameBounds (U U_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedExponentialShiftDerivative (coefficient)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open GaussianSineProductImaginaryHyperbolic (expF expData)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Scale" => GaussianPiRationalScale.nameF
local notation "Pi" => GaussianGammaHalfPiName.nameF

def incrementF : PR 2 := GaussianNamedDifference.nameF expF expF
def incrementData (s : Bool) (A B k R x : PTm n) : PTm n :=
  GaussianNamedDifference.data (expData s (k*A+one) (k*B) R x) (expData s A B R x)
def weightedF : PR 2 := multiplyF expF Scale
def weightedData (s : Bool) (A B k R x : PTm n) : PTm n :=
  multiplyData expF Scale (expData s A B R x) (GaussianPiRationalScale.data s one (k*B) R x)
def errorCoefficient (s : Bool) (A B R x : PTm n) : PTm n :=
  U expF (expData s A B R x)*(U Pi x*U Pi x)

def source (A B k R x : PTm n) : Fm PTm n :=
  le one R ⋏ (le one B ⋏ (le one k ⋏
    (le A (R*B) ⋏ (le (k*A+one) (R*(k*B)) ⋏ le (U Pi x) (k*B)))))

theorem increment_rate (s : Bool) (A B k R x : PTm n) (h : Γ ⊢[PRAAx] source A B k R x) : Γ ⊢[PRAAx]
    independentRate incrementF weightedF (incrementData s A B k R x) (weightedData s A B k R x)
      (errorCoefficient s A B R x) ((k*B)*(k*B)) := by
  let v := GaussianPiRationalScale.data s A B R x
  let w := GaussianPiRationalScale.data s (k*A) (k*B) R x
  let z := GaussianPiRationalScale.data s one (k*B) R x
  let y := GaussianPiRationalScale.data s (k*A+one) (k*B) R x
  let S := R*U Pi x
  let E := k*B
  have hR := h.andE₁
  have hB := h.andE₂.andE₁
  have hk := h.andE₂.andE₂.andE₁
  have hA := h.andE₂.andE₂.andE₂.andE₁
  have hy := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hz := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have hE : Γ ⊢[PRAAx] le one E := positive_product k B hk hB
  have hs : Γ ⊢[PRAAx] le one S := positive_product _ _ hR (U_positive Pi x)
  have hZ : Γ ⊢[PRAAx] le one (R*E) := positive_product _ _ hR hE
  have hv := GaussianPiRationalScale.exponential_input s A B R x hB hA
  have ht := GaussianPiRationalScale.exponential_input s (k*A+one) E R x hE hy
  have hw := GaussianPiRationalScale.regular s (k*A) E R x hE (le_trans (le_add_right _ _) hy)
  have small := GaussianPiRationalScale.small_source s one E R x hE hZ
    (le_congr (one_mul _).eqSymm (.eqRefl _) hz)
  have eStep := GaussianPiRationalScale.exponential_input s one E R x hE hZ
  have eV := GaussianPiRationalScaleRepresentation.rescale s A B k R x hB hk hA
  have sum := GaussianPiRationalScale.addition s (k*A) E one R x hE hy
  have replace := add_cross Scale Scale Scale Scale w v z z hw hv.andE₁ eStep.andE₁ eStep.andE₁ eV
    (cross_refl Scale z eStep.andE₁)
  have move := cross_trans _ _ _ _ _ _ sum replace
  have sumInput := GaussianExponentialReference.add_input Scale Scale S v z hv eStep
  have expMove := GaussianExponentialRadiusIndependence.independent_radii_proper
    Scale (addF Scale Scale) S (S+S) y (addData v z) ht sumInput move
  have eBase := GaussianRadiusExponentialName.name_regular Scale S v hv
  have eLater := GaussianRadiusExponentialName.name_regular Scale S y ht
  have eSum := GaussianRadiusExponentialName.name_regular (addF Scale Scale) (S+S) (addData v z) sumInput
  have inc := difference_proper expF (GaussianExponentialAddition.sumF Scale Scale) expF expF
    (expData s (k*A+one) E R x) (GaussianExponentialAddition.sumData S v z) (expData s A B R x) (expData s A B R x)
    eLater eSum eBase eBase expMove (cross_refl _ _ eBase)
  have estimate := GaussianNamedExponentialShiftDerivative.independent_rate Scale Scale S v z (one*U Pi x) E hs hv small
  have hwgt := GaussianNameArithmetic.multiply_fast expF Scale (expData s A B R x) z eBase eStep.andE₁
  have result := GaussianNamedRateTransport.transport _ _ incrementF weightedF _ _ _ _
    (coefficient Scale S v (one*U Pi x)) (E*E) (positive_product E E hE hE) estimate inc (cross_refl _ _ hwgt)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by dsimp only [coefficient,errorCoefficient,S,v,expF,expData]; ipra_ring) (.eqRefl _) result

theorem actual_imaginary_sine_shifted_exponential_rate_closed (s : Bool) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      independentRate incrementF weightedF
        (incrementData s (var 0) (var 1) (var 2) (var 3) (var 4))
        (weightedData s (var 0) (var 1) (var 2) (var 3) (var 4))
        (errorCoefficient s (var 0) (var 1) (var 3) (var 4)) ((var 2*var 1)*(var 2*var 1))) :=
  closeUniv 5 (.impI (increment_rate s _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryExponentialShift
