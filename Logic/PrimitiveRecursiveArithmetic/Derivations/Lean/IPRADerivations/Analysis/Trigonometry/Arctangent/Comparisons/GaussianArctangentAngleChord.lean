import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.Correctness.GaussianArctangentInverseCorrectness
import IPRADerivations.Analysis.Trigonometry.Arctangent.Comparisons.GaussianArctangentImaginaryOrderTransport
import IPRADerivations.Analysis.Trigonometry.Arctangent.Extension.GaussianArctangentNamedChordExtension
import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.NamedValues.GaussianArctangentNamedCayleyTrig
import IPRADerivations.Analysis.Trigonometry.Sine.GaussianNamedSineFromExponential

/-!
# The sine chord on the full certified angle interval

Apply the arctangent chord at the proved inverse of the input angle.
The exact round trip identifies the angle, and properness of sine,
multiplication and imaginary-coordinate order identifies both sides
at independent precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentAngleChord

open_ipra
open GaussianArctangentInverseForward (input imaginaryOrder)
open GaussianArctangentInverseCorrectness (roundTripF imaginarySamples imaginary_right_inverse)
open GaussianArctangentNamedInverse (data)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianNamedSineFromExponential (sineF sineData sine_regular sine_proper)
open GaussianNameArithmetic (multiplyF multiplyData multiply_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl cross_to_diagonal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def productF (f : PR 2) : PR 2 := multiplyF (sineF f) quarterF
def productData (f : PR 2) (x z : PTm n) : PTm n :=
  multiplyData (sineF f) quarterF (sineData f (GaussianNameBounds.U f x) x) z

private theorem transport_chord (f : PR 2) (x z : PTm n) (h : Γ ⊢[PRAAx] input f x z)
    (hi : Γ ⊢[PRAAx] imaginarySamples f x)
    (hSin : Γ ⊢[PRAAx] crossEquivalent (sineF (roundTripF f))
      (GaussianArctangentNamedChordExtension.sineF (GaussianArctangentNamedInverse.nameF f))
      (sineData (roundTripF f) two (data x)) (GaussianArctangentNamedChordExtension.sineData (data x))) :
    Γ ⊢[PRAAx] imaginaryOrder f (productF f) x (productData f x z) := by
  let inv := GaussianArctangentNamedInverse.nameF f
  let g := roundTripF f
  let y := data x
  let R := GaussianNameBounds.U f x
  let s := GaussianArctangentNamedChordExtension.sineF inv
  let b := GaussianArctangentNamedChordExtension.sineData y
  have hInv := GaussianArctangentNamedInverse.name_regular f x z h
  have hG : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input g two y :=
    GaussianArctangentNamedCayley.exp_input inv y hInv
  have hF : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x :=
    GaussianGammaFiniteApproximantName.exponential_input f x h.andE₁
  have eqAngle := imaginary_right_inverse f x z h hi
  have eqSin := cross_trans s (sineF g) (sineF f) b (sineData g two y) (sineData f R x)
    (cross_symm _ _ _ _ hSin) (sine_proper g f two R y x hG hF eqAngle)
  have hQuarter := quarter_regular (Γ := Γ) z
  have eqProd := multiply_equivalent s (sineF f) quarterF quarterF b (sineData f R x) z z
    (GaussianArctangentNamedChordExtension.sine_regular inv y hInv) (sine_regular f R x hF) hQuarter hQuarter
    (cross_to_diagonal _ _ _ _ eqSin) (cross_to_diagonal _ _ _ _ (cross_refl _ _ hQuarter))
  exact GaussianArctangentImaginaryOrderTransport.imaginary_order_congr _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ eqAngle) eqProd (GaussianArctangentNamedChordExtension.original_chord inv y z hInv)

theorem original_chord (f : PR 2) (x z : PTm n) (h : Γ ⊢[PRAAx] input f x z)
    (hi : Γ ⊢[PRAAx] imaginarySamples f x) :
    Γ ⊢[PRAAx] imaginaryOrder f (productF f) x (productData f x z) :=
  transport_chord f x z h hi
    (GaussianArctangentNamedCayleyTrig.sine_cross (GaussianArctangentNamedInverse.nameF f) (data x)
      (GaussianArctangentNamedInverse.name_regular f x z h))

theorem actual_original_sine_chord_on_angle_interval_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (input f (var 0) (var 1) ⟶ imaginarySamples f (var 0) ⟶
        imaginaryOrder f (productF f) (var 0) (productData f (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (original_chord f _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentAngleChord
