import IPRADerivations.Analysis.Polynomials.RationalReverseChebyshevCell
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderBernoulliMeshMargin
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPairedRefinement

/-!
# A positive crossed-product gap on separated Bernoulli grid boxes

Combine the native centered Bernoulli gap and the reflected
inverse-power weight gap on the two separated rational subintervals.
Their product is a single positive margin independent of refinement.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBoxProductGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianPositiveRealArithmetic (sign)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_lower nonnegative_of_representation)
open GaussianStirlingAllOrderBernoulliMeshMargin (margin coarseDen positive_margin separated_mesh_margin)
open GaussianStirlingAllOrderCenteredBernoulli (sample sample_canonical denominator_positive)
open GaussianStirlingAllOrderPairedRefinement (mesh start lowerCenter upperCenter centerGap center_gap_positive separated_grid_gap)
open GaussianStirlingAllOrderPairedWeight (pairWeight gapDenominator gap_denominator_positive)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open RationalArithmetic (add multiply multiply_monotone)
open RationalNonnegativePowers (fraction_multiply fraction_congr)
open RationalNormalForm (wellFormed normalize_well_formed)
open RationalReverseChebyshevCell (rectangle_margin)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

noncomputable def sampleAt (m : ℕ) (S p : PTm n) : PTm n := sample (m+1) p (S*num 8)
def weightAt (q A B S p : PTm n) : PTm n := pairWeight q (mesh B S) (start A S) (B*p)
noncomputable def boxMargin (m : ℕ) (q A B : PTm n) : PTm n := multiply (margin m) (centerGap q A B)
def weightDenominator (q A B : PTm n) : PTm n := gapDenominator q (num 8*A+B) (two*B) (num 4*B)

theorem box_margin_positive (m : ℕ) (q A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] rationalLE (fraction one (coarseDen m*weightDenominator q A B)) (boxMargin m q A B) := by
  let r : PTm n := coarseDen m
  let s := weightDenominator q A B
  let c := fraction one r
  let d := fraction one s
  let p : PTm n := margin m
  let t := centerGap q A B
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := by ipra_le 7
  have hr : Γ ⊢[PRAAx] le one r := denominator_positive _ _ h8
  have hp : Γ ⊢[PRAAx] le one (num 8*A+B) := le_trans (positive_product _ _ h8 hA) (le_add_right _ _)
  have hs : Γ ⊢[PRAAx] le one s := gap_denominator_positive _ _ _ _ hp
  have hc := nonnegative_of_representation c one r hr (fraction_represents one r hr)
  have hd := nonnegative_of_representation d one s hs (fraction_represents one s hs)
  have lu : Γ ⊢[PRAAx] rationalLE d t := center_gap_positive _ _ _ hA hB
  have lt := nonnegative_of_lower d t hd lu
  have first := multiply_monotone c d t hc lu
  have second := rationalLE_congr (RationalAlgebra.multiply_commutative t c) (RationalAlgebra.multiply_commutative t p)
    (multiply_monotone t c p lt (positive_margin m))
  have f := (fraction_multiply one r one s hr hs).eqTrans (fraction_congr (one_mul one) (.eqRefl _))
  exact rationalLE_congr f (.eqRefl _) (transitive first second)

theorem box_product_gap (m : ℕ) (q A B S i j : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S)
    (hi : Γ ⊢[PRAAx] le i (S*one)) (hj : Γ ⊢[PRAAx] le (S*num 3) j)
    (hM : Γ ⊢[PRAAx] le (two*j) (S*num 8)) :
    Γ ⊢[PRAAx] rationalLE
      (add (add (multiply (sampleAt m S i) (weightAt q A B S i)) (multiply (sampleAt m S j) (weightAt q A B S j)))
        (boxMargin m q A B))
      (add (multiply (sampleAt m S i) (weightAt q A B S j)) (multiply (sampleAt m S j) (weightAt q A B S i))) := by
  let H := sampleAt m S i
  let H' := sampleAt m S j
  let W := weightAt q A B S i
  let W' := weightAt q A B S j
  let C : PTm n := margin m
  let D := centerGap q A B
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := by ipra_le 7
  have hm := positive_product _ _ hS h8
  have near : Γ ⊢[PRAAx] le (B*i) (lowerCenter B S) := by
    unfold lowerCenter
    exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right B hi)
  have far : Γ ⊢[PRAAx] le (upperCenter B S) (B*j) := by
    unfold upperCenter
    exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right B hj)
  have guard : Γ ⊢[PRAAx] le (two*(B*j)) (mesh B S) := by
    unfold mesh
    exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right B hM)
  have left : Γ ⊢[PRAAx] rationalLE (add H C) H' := separated_mesh_margin m S i j hS hi hj hM
  have right : Γ ⊢[PRAAx] rationalLE (add W' D) W := separated_grid_gap q A B S _ _ hA hS near far guard
  have cD : Γ ⊢[PRAAx] le one (coarseDen m : PTm n) := denominator_positive _ _ h8
  let base := num 8*A+B
  have hp : Γ ⊢[PRAAx] le one base := le_trans (positive_product _ _ h8 hA) (le_add_right _ _)
  have dD := gap_denominator_positive q base (two*B) (num 4*B) hp
  have cS : Γ ⊢[PRAAx] sign C := nonnegative_of_lower _ _ (nonnegative_of_representation _ _ _ cD
    (fraction_represents one (coarseDen m) cD)) (positive_margin m)
  have dS : Γ ⊢[PRAAx] sign D := nonnegative_of_lower _ _ (nonnegative_of_representation _ _ _ dD
    (fraction_represents one (gapDenominator q base (two*B) (num 4*B)) dD)) (center_gap_positive q A B hA hB)
  have cCan : Γ ⊢[PRAAx] wellFormed C := normalize_well_formed _ _ cD
  have dCan : Γ ⊢[PRAAx] wellFormed D := normalize_well_formed _ _ dD
  exact rectangle_margin H H' W W' C D (sample_canonical _ _ _ hm) (RationalArithmetic.add_guard _ _) cCan dCan cS dS left right

theorem actual_Bernoulli_reflected_box_product_gap_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((le one (var 1) ⋏ (le one (var 2) ⋏ le one (var 3))) ⟶
        (le (var 4) (var 3*one) ⋏ (le (var 3*num 3) (var 5) ⋏ le (two*var 5) (var 3*num 8))) ⟶
        rationalLE
          (add (add
            (multiply (sampleAt m (var 3) (var 4)) (weightAt (var 0) (var 1) (var 2) (var 3) (var 4)))
            (multiply (sampleAt m (var 3) (var 5)) (weightAt (var 0) (var 1) (var 2) (var 3) (var 5))))
            (boxMargin m (var 0) (var 1) (var 2)))
          (add (multiply (sampleAt m (var 3) (var 4)) (weightAt (var 0) (var 1) (var 2) (var 3) (var 5)))
            (multiply (sampleAt m (var 3) (var 5)) (weightAt (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 6 (.impI (.impI (box_product_gap m _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBoxProductGap
