import IPRADerivations.Analysis.Stirling.AllOrders.FirstPanel.GaussianStirlingAllOrderFirstPanelSum
import IPRADerivations.Analysis.RationalArithmetic.RationalHalfNinthProductLower

/-!
# Scaled inverse-square error in the first centered panel

After the exact normalization of the panel, its weighted reciprocal-square
sum approaches one with a rational one-sided error. The estimate holds on
every original harmonic mesh and retains all dependence on U, B and Q.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelSquareError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderSquareIntegral (inverse finite_error)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_representation)
open RationalNonnegativePowers (fraction_multiply)
open RationalReciprocalPowerTail (tail)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr add_associative add_commutative multiply_add)
open RationalArgmin (rationalLE rationalLE_congr reflexive)
open GaussianRationalSyntheticBounds (add_monotone)
open RationalHalfNinthProductLower (add_negative_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weight (U B Q : PTm n) : PTm n := fraction (U*(U+B)*Q) B
def squareContribution (U B Q : PTm n) : PTm n := multiply (weight U B Q) (tail two (Q*U) (B*Q))
def squareError (U B Q : PTm n) : PTm n := fraction (U+B) (B*succ (Q*U))

private theorem equal_fractions (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] a*d ≐ c*b) :
    Γ ⊢[PRAAx] fraction a b ≐ fraction c d := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hb) (RationalNormalForm.normalize_well_formed _ _ hd)
    (fraction_represents _ _ hb) (fraction_represents _ _ hd) hb hd
  apply ZT.derive (u := ZT.ofNat a*ZT.ofNat d) (v := ZT.ofNat c*ZT.ofNat b)
  have e := natEq h
  ipra_simps
  exact e

private theorem sum_unit (U B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] add (fraction one one) (fraction U B) ≐ fraction (U+B) B := by
  have hD := positive_product _ _ (le_refl one) hB
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.add_guard _ _) (RationalNormalForm.normalize_well_formed _ _ hB)
    (RationalRepresentations.represents_add _ _ _ _ _ _ (fraction_represents one one (le_refl one)) (fraction_represents U B hB))
    (fraction_represents _ _ hB) hD hB
  apply ZT.derive
  ipra_simps
  ring

theorem square_contribution_error (U B Q : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] rationalLE (squareContribution U B Q) (fraction one one) ⋏
      rationalLE (fraction one one) (add (squareContribution U B Q) (squareError U B Q)) := by
  let N := Q*U
  let L := B*Q
  let w := weight U B Q
  let c := U*(U+B)*Q
  let T := tail two N L
  let P := multiply w (inverse (N+L))
  let W := squareContribution U B Q
  let E := squareError U B Q
  let u : PTm n := fraction one one
  have hN := positive_product _ _ hQ hU
  have hNL := le_trans hN (le_add_right N L)
  have hw := nonnegative_of_representation w c B hB (fraction_represents c B hB)
  have eN : Γ ⊢[PRAAx] multiply w (inverse N) ≐ fraction (U+B) B :=
    (fraction_multiply c B one N hB hN).eqTrans
      (equal_fractions _ _ _ _ (positive_product _ _ hB hN) hB (by dsimp [c,N]; ipra_ring))
  have eNL : Γ ⊢[PRAAx] P ≐ fraction U B :=
    (fraction_multiply c B one (N+L) hB hNL).eqTrans
      (equal_fractions _ _ _ _ (positive_product _ _ hB hNL) hB (by dsimp [c,N,L]; ipra_ring))
  have eK : Γ ⊢[PRAAx] multiply w (inverse N) ≐ add u P :=
    eN.eqTrans ((sum_unit U B hB).eqSymm.eqTrans (add_congr (.eqRefl _) eNL.eqSymm))
  have hD : Γ ⊢[PRAAx] le one (N*succ N) := positive_product _ _ hN (zero_lt_succ _)
  have hE := positive_product _ _ hB (zero_lt_succ N)
  have eE : Γ ⊢[PRAAx] multiply w (GaussianStirlingAllOrderSquareIntegral.error N) ≐ E :=
    (fraction_multiply c B one (N*succ N) hB hD).eqTrans
      (equal_fractions _ _ _ _ (positive_product _ _ hB hD) hE (by dsimp [c,N,E,squareError]; ipra_ring))
  have eT : Γ ⊢[PRAAx] multiply w (add T (inverse (N+L))) ≐ add W P := multiply_add _ _ _
  have old := finite_error N L hN
  have upper := rationalLE_congr eT eK (RationalArithmetic.multiply_monotone w _ _ hw old.andE₁)
  have lower := rationalLE_congr eK
    ((multiply_add _ _ _).eqTrans (add_congr eT eE)) (RationalArithmetic.multiply_monotone w _ _ hw old.andE₂)
  have swapped : Γ ⊢[PRAAx] add (add W P) E ≐ add (add W E) P :=
    (add_associative _ _ _).eqTrans ((add_congr (.eqRefl _) (add_commutative _ _)).eqTrans (add_associative _ _ _).eqSymm)
  have fixed := reflexive (Γ := Γ) (negative P)
  have wc := RationalArithmetic.multiply_guard (Γ := Γ) w T
  have uc := RationalNormalForm.normalize_well_formed (Γ := Γ) (ZT.ofNat one) one (le_refl one)
  have result := add_monotone _ _ _ _ (rationalLE_congr (.eqRefl _) swapped lower) fixed
  exact .andI
    (rationalLE_congr (add_negative_cancel W P wc) (add_negative_cancel u P uc) (add_monotone _ _ _ _ upper fixed))
    (rationalLE_congr (add_negative_cancel u P uc) (add_negative_cancel (add W E) P (RationalArithmetic.add_guard _ _)) result)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelSquareError
