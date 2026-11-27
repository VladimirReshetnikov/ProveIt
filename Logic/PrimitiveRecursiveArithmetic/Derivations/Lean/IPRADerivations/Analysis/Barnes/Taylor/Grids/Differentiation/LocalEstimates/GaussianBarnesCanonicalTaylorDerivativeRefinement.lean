import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.CofinalIdentities.GaussianBarnesCanonicalTaylorAllOrderDerivative
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeChart

/-!
# Certified nonzero steps at every Barnes factorial order

At any admitted rational center, a common positive integer rescaling
leaves the center fixed and provides a positive real rational step of
arbitrarily small prescribed size. The next factorial coefficient name
is read on the original rational presentation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeRefinement

open_ipra
open ComplexLogarithmRemainder (add bounded bounded_add bounded_mono bounded_scale normSq normSq_one oneCode scale)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorAllOrderDerivative (stepClock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianL1 (norm1 norm1_one)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianBarnesCanonicalTaylorNamedQuotient.nameF
local notation "qd" => GaussianBarnesCanonicalTaylorNamedQuotient.data
local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data

def refinement (p R e : PTm n) : PTm n := unit (stepClock p (R+one) e)

private theorem retained_next (e : PTm n) : Γ ⊢[PRAAx] le (succ e) (previous (pred e)) := by
  apply Common.succ_le_succ
  refine .orE (lt_or_le zero e) ?_ ?_
  · exact le_congr (.eqRefl e) (Common.pos_of_one_le Prf.hyp0) (le_refl e)
  · exact le_trans Prf.hyp0 (zero_le _)

private theorem widen (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] source z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

theorem certified (p z R B J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous J)) :
    let A := refinement p R e
    let w := scale A z
    let C := A*B
    Γ ⊢[PRAAx] (ofGaussian w C ≐ ofGaussian z B) ⋏ le (unit p) C ⋏
      independentRate Q F (qd w oneCode (R+one) C J e) (fd z ((R+one)+one) B (pred e) (succ e)) one (unit p) := by
  let S := R+one
  let T := S+one
  let A := refinement p R e
  let w := scale A z
  let C := A*B
  have hA := unit_positive (Γ := Γ) (stepClock p S e)
  have hC : Γ ⊢[PRAAx] le one C := positive_product A B hA hz.andE₁
  have fit : Γ ⊢[PRAAx] le A C :=
    le_congr (one_mul A) (mul_comm B A) (mul_le_mul_right A hz.andE₁)
  have hzA : Γ ⊢[PRAAx] source w R C :=
    .andI hC (le_congr (.eqRefl _) (by dsimp only [C]; ipra_ring) (bounded_scale A hz.andE₂))
  have hbase := widen w R C hzA
  have one_bound : Γ ⊢[PRAAx] bounded oneCode one :=
    le_congr normSq_one.eqSymm (one_mul one).eqSymm (le_refl one)
  have next : Γ ⊢[PRAAx] source (add w oneCode) S C :=
    .andI hC (le_congr (.eqRefl _) (by dsimp only [S,C]; ipra_ring)
      (bounded_add hzA.andE₂ (bounded_mono one_bound hC)))
  have nonzero : Γ ⊢[PRAAx] le one (normSq (oneCode : PTm n)) :=
    le_congr (.eqRefl _) normSq_one.eqSymm (le_refl one)
  have small : Γ ⊢[PRAAx] le (norm1 oneCode*unit (stepClock p S e)) C :=
    le_congr ((congrMul norm1_one (.eqRefl A)).eqTrans (one_mul A)).eqSymm (.eqRefl _) fit
  have same := GaussianGammaEncodingRescaling.fraction_rescale z B A hz.andE₁ hA
  have raw := GaussianBarnesCanonicalTaylorAllOrderDerivative.rate p w oneCode S C J e hbase next nonzero he small
  have hx := GaussianBarnesCanonicalTaylorNamedQuotient.regular w oneCode S C J e hbase next nonzero he
  have htarget := GaussianBarnesCanonicalTaylorDerivativeChart.cofinal_cross z w T B C (pred e) (succ e)
    (widen z S B (widen z R B hz)) (widen w S C hbase) (retained_next e) same.eqSymm
  have pay : Γ ⊢[PRAAx] le p (stepClock p S e) := by
    unfold stepClock GaussianBarnesCanonicalTaylorDerivativeBase.stepClock GaussianFastValueCut.exponent
    exact le_trans (le_add_right p _) (le_add_right _ _)
  exact .andI same (.andI (le_trans (unit_monotone pay) fit)
    (GaussianNamedRateTransport.transport Q F Q F (qd w oneCode S C J e) (fd w T C (pred e) (succ e))
      (qd w oneCode S C J e) (fd z T B (pred e) (succ e)) one (unit p) (unit_positive p) raw (cross_refl _ _ hx) htarget))

theorem actual_Barnes_all_order_arbitrarily_small_derivative_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let p := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let J := var 4
     let e := var 5
     let A := refinement p R e
     let w := scale A z
     let C := A*B
     (source z R B ⋏ le e (previous J)) ⟶ (ofGaussian w C ≐ ofGaussian z B) ⋏ le (unit p) C ⋏
       independentRate Q F (qd w oneCode (R+one) C J e) (fd z ((R+one)+one) B (pred e) (succ e)) one (unit p)) :=
  closeUniv 6 (.impI (certified _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeRefinement
