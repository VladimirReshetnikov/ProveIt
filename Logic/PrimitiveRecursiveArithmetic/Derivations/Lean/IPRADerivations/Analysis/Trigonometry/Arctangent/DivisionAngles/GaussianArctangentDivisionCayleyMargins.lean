import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionInverseMargins
import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianArctangentInverseCayleySamples
import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionAngleResidual
import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.Coordinates.GaussianArctangentCayleySineMargin

/-!
# Positive margins on the actual divided-angle Cayley observations

The normalized inverse parameters all represent fractions on the same
literal grid. Sine lower bounds and pairwise separation of squared
sines transfer from that grid to the samples used by the residual proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentDivisionCayleyMargins

open_ipra
open GaussianArctangentCayleyProjections (sine_projection)
open GaussianArctangentCayleySineMargin (lower_of_grid_margin)
open GaussianArctangentCayleySquareGap (squareValue separationDenominator rational_gap marginSource)
open GaussianArctangentCayleyTrig (sinePoint)
open GaussianArctangentDivisionAngles (modulus)
open GaussianArctangentDivisionAngleResidual (inverseF inverseData sineSample)
open GaussianArctangentDivisionInverseMargins (inverseIndex inverse_start inverse_margins)
open GaussianArctangentInverseCayleySamples (inversePrecision raw_at)
open GaussianArctangentInverseSampler (mesh mesh_positive index_le)
open GaussianArctangentNamedCayley (queryPrecision)
open GaussianCoefficientNameBounds (unit)
open GaussianNameReciprocal (lower lower_congr)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open RationalArithmetic (add add_at addF)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalCubeMidpoint (fraction)
open RationalGaussianRealPart (embed_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def precision (p : PTm n) : PTm n := inversePrecision (queryPrecision p)

theorem sine_readback (p k J z : PTm n) :
    Γ ⊢[PRAAx] sineSample p k J z ≐ sinePoint (mesh (precision p)) (inverseIndex k J z (precision p)) := by
  let A := GaussianArctangentDivisionAngleResidual.index p k J z
  let B := GaussianArctangentDivisionAngleResidual.mesh p k J z
  let M := mesh (precision p)
  let i := inverseIndex k J z (precision p)
  have hB := GaussianArctangentDivisionAngleResidual.mesh_positive (Γ := Γ) p k J z
  have hM := mesh_positive (Γ := Γ) (precision p)
  have rawEq : Γ ⊢[PRAAx] GaussianArctangentCayleyValues.value B A ≐ GaussianArctangentCayleyValues.value M i :=
    raw_at GaussianArctangentDivisionAngles.nameF p (GaussianArctangentDivisionAngles.data k (modulus J) z)
  exact (sine_projection B A hB).eqSymm.eqTrans ((embed_congr (congrSnd rawEq)).eqTrans (sine_projection M i hM))

theorem sine_lower_at (p k J z : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hJ : Γ ⊢[PRAAx] le k J)
    (hfine : Γ ⊢[PRAAx] le (num 14*modulus J) (unit (precision p))) :
    Γ ⊢[PRAAx] lower (sineSample p k J z) (num 4*modulus J) := by
  let t := precision p
  let T := num 4*modulus J
  let M := mesh t
  let i := inverseIndex k J z t
  have hm : Γ ⊢[PRAAx] le one (modulus J) := zero_lt_succ _
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring)) hm
  have hi : Γ ⊢[PRAAx] le i M := index_le GaussianArctangentDivisionAngles.nameF t
    (GaussianArctangentDivisionAngles.data k (modulus J) z)
  exact lower_congr (sine_readback p k J z).eqSymm (.eqRefl T)
    (lower_of_grid_margin M i T (mesh_positive t) hT hi (inverse_start k J z t hk hJ hfine))

def squareSample (p k J z : PTm n) : PTm n := fstT (qmul (sineSample p k J z) (sineSample p k J z))

theorem squared_sine_gap_at (p k l J z : PTm n) (hk : Γ ⊢[PRAAx] le one k) (hkl : Γ ⊢[PRAAx] lt k l)
    (hJ : Γ ⊢[PRAAx] le l J) (hfine : Γ ⊢[PRAAx] le (num 28*modulus J) (unit (precision p))) :
    Γ ⊢[PRAAx] rationalLE
      (add (squareSample p k J z) (fraction one (separationDenominator (num 4*modulus J))))
      (squareSample p l J z) := by
  let t := precision p
  let T := num 4*modulus J
  let D := fraction one (separationDenominator T)
  let M := mesh t
  let i := inverseIndex k J z t
  let j := inverseIndex l J z t
  have h : Γ ⊢[PRAAx] marginSource M i j T :=
    inverse_margins k l J z t hk (le_congr (by ipra_ring) (.eqRefl _) hkl) hJ hfine
  have gap := rational_gap M i j T h.andE₁.andE₁ h.andE₁.andE₂ h.andE₂.andE₁.andE₁ h.andE₂.andE₁.andE₂
    h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂
  have ek := sine_readback (Γ := Γ) p k J z
  have el := sine_readback (Γ := Γ) p l J z
  have a : Γ ⊢[PRAAx] squareSample p k J z ≐ squareValue M i := congrFst (qmul_congr ek ek)
  have b : Γ ⊢[PRAAx] squareSample p l J z ≐ squareValue M j := congrFst (qmul_congr el el)
  have left := (add_at (squareSample p k J z) D).eqSymm.eqTrans
    ((congrAp2 addF a (.eqRefl D)).eqTrans (add_at (squareValue M i) D))
  exact rationalLE_congr left.eqSymm b.eqSymm gap

end LeanProofs.IPRA.Analysis.GaussianArctangentDivisionCayleyMargins
