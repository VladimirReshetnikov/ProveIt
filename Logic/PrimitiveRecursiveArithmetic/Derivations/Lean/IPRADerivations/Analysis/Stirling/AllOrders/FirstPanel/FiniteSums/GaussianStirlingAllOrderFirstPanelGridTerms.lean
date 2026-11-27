import IPRADerivations.Analysis.Stirling.AllOrders.FirstPanel.GaussianStirlingAllOrderFirstPanel
import IPRADerivations.Analysis.Stirling.AllOrders.PowerIntegrals.GaussianStirlingAllOrderSquareIntegral
import IPRADerivations.Analysis.Stirling.AllOrders.PowerIntegrals.GaussianStirlingAllOrderHarmonicIntegral

/-!
# First-order split at the original harmonic logarithm grid

With mesh BQ and x = U/B at the start of the panel, the exact
sample is a constant plus weights on 1/(QU+r) and 1/(QU+r)^2.
The weights are fixed inside each finite sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelGridTerms

open_ipra
open GaussianStirlingAllOrderFirstPanel (first_kernel_decomposition splitRow splitNumerator base)
open GaussianStirlingAllOrderKernel (row offset offset_positive)
open GaussianStirlingAllOrderSquareIntegral (reciprocal_square)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (multiply_congr add_congr negative_congr)
open RationalRepresentations (represents_add represents_negative)
open RationalReciprocalPowerTail (reciprocalPower)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def linearCoefficient (U B Q : PTm n) : PTm n := (two*U+B)*Q
def squareCoefficient (U B Q : PTm n) : PTm n := U*(U+B)*(Q*Q)
def gridIndex (U Q r : PTm n) : PTm n := Q*U+r

def parts (U B Q r : PTm n) : PTm n :=
  let C := gridIndex U Q r
  add (negative (fraction one one))
    (add (multiply (fraction (linearCoefficient U B Q) one) (reciprocalPower one C))
      (negative (multiply (fraction (squareCoefficient U B Q) one) (reciprocalPower two C))))

ipra_subst parts [gridIndex, linearCoefficient, squareCoefficient]

theorem grid_parts (A B Q k r : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) (hr : Γ ⊢[PRAAx] le r (B*Q)) :
    Γ ⊢[PRAAx] row 0 one A B (B*Q) k r ≐ parts (A+B*k) B Q r := by
  let U := A+B*k
  let M := B*Q
  let C := gridIndex U Q r
  let D := base A B M k r
  let E := linearCoefficient U B Q
  let F := squareCoefficient U B Q
  let x := fraction E C
  let y := fraction F (C*C)
  let z : PTm n := negative (fraction one one)
  have hM := positive_product _ _ hB hQ
  have hC : Γ ⊢[PRAAx] le one C :=
    le_trans (positive_product _ _ hQ (le_trans hA (le_add_right A (B*k)))) (le_add_right _ _)
  have hCC := positive_product _ _ hC hC
  have hD : Γ ⊢[PRAAx] le one D := le_trans (offset_positive A B M k hA hM) (le_add_right _ _)
  have hDD := positive_product _ _ hD hD
  have hP := positive_product _ _ hC hCC
  have e₁ : Γ ⊢[PRAAx] multiply (fraction E one) (reciprocalPower one C) ≐ x :=
    (multiply_congr (.eqRefl _) (fraction_congr (.eqRefl _) (pw_one C))).eqTrans
      ((fraction_multiply E one one C (le_refl one) hC).eqTrans
        (fraction_congr (by ipra_ring) (one_mul C)))
  have e₂ : Γ ⊢[PRAAx] multiply (fraction F one) (reciprocalPower two C) ≐ y :=
    (multiply_congr (.eqRefl _) (reciprocal_square C)).eqTrans
      ((fraction_multiply F one one (C*C) (le_refl one) hCC).eqTrans
        (fraction_congr (by ipra_ring) (one_mul (C*C))))
  have e : Γ ⊢[PRAAx] parts U B Q r ≐ add z (add x (negative y)) :=
    add_congr (.eqRefl _) (add_congr e₁ (negative_congr e₂))
  refine (first_kernel_decomposition A B M k r hA hM hr).eqTrans (?_ : Γ ⊢[PRAAx] splitRow A B M k r ≐ add z (add x (negative y))) |>.eqTrans e.eqSymm
  have v₀ := represents_negative _ _ _ (fraction_represents (Γ := Γ) one one (le_refl one))
  have v₁ := fraction_represents E C hC
  have v₂ := represents_negative _ _ _ (fraction_represents F (C*C) hCC)
  have vv := represents_add _ _ _ _ _ _ v₁ v₂
  have rep := represents_add _ _ _ _ _ _ v₀ vv
  let V := -ZT.ofNat one*ZT.ofNat (C*(C*C))+
    (ZT.ofNat E*ZT.ofNat (C*C)+(-ZT.ofNat F)*ZT.ofNat C)*ZT.ofNat one
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hDD) (RationalArithmetic.add_guard _ _)
    (RationalIntegerNormalization.normalize_preserves_value _ _ hDD) rep hDD
    (positive_product _ _ (le_refl one) hP)
  apply ZT.derive (u := splitNumerator A B M k r*ZT.ofNat (one*(C*(C*C)))) (v := V*ZT.ofNat (D*D))
  dsimp only [V,splitNumerator,E,F,D,C,M,U,base,offset,gridIndex,linearCoefficient,squareCoefficient]
  ipra_simps
  ring

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelGridTerms
