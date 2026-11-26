import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelPartsOuterFold

/-!
# Solving the finite recurrence for the higher original kernel

The division is by the fixed positive derivative coefficient.
Its reciprocal is at most one, so solving the recurrence preserves
the quantitative finite error.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsSolve

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderPanelPartsOuter (finite_outer_recurrence)
open GaussianStirlingAllOrderPanelPartsOuterFold (massPrefix panelPrefix fold_identity)
open GaussianStirlingAllOrderPanelPartsRecurrence (errorCoefficient)
open GaussianStirlingAllOrderPanelPartsDensities (lowScalar highScalar)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderReciprocalWeightError (coefficient)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianStirlingAllOrderPanelPartsRows (scalar_order_bound)
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qsub_congr qadd_congr)
open RationalArithmetic (multiply negative)
open RationalAlgebra (multiply_congr multiply_commutative multiply_associative multiply_add
  multiply_negative add_congr negative_congr)
open RationalSumConstants (multiply_one_right)
open RationalGaussianEmbedding (embed embed_add embed_multiply embed_negative)
open RationalGaussianRealPart (embed_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseHigh (e : ℕ) : PTm n := fraction one (coefficient e)
def ratio (m e : ℕ) : PTm n := multiply (inverseHigh e) (lowScalar m)

def estimate (m e : ℕ) (A B M L : PTm n) : PTm n :=
  multiply (ratio m e)
    (sub (multiply (signedMean m) (massPrefix e A B M L)) (panelPrefix (m-1) (e-1) A B M L))

theorem coefficient_positive (e : ℕ) (he : 2≤e) : Γ ⊢[PRAAx] le one (coefficient e : PTm n) :=
  Foundations.NumeralPrimes.num_le (a := 1) (by
    unfold GaussianStirlingAllOrderReciprocalTaylor.secondCoefficient
    have h : 1≤e := by omega
    exact Nat.mul_pos h (Nat.succ_pos e))

theorem inverse_high_bounded (e : ℕ) (he : 2≤e) : Γ ⊢[PRAAx] bounded (embed (inverseHigh e : PTm n)) one one := by
  let D : PTm n := coefficient e
  have hD := coefficient_positive (Γ := Γ) e he
  have lo := fraction_order zero one one D (le_refl one) hD (by ipra_le 1)
  have hi := fraction_order one D one one hD (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) hD)
  exact scalar_order_bound _ _ _ (le_refl one) lo hi

theorem inverse_high_cancel (e : ℕ) (he : 2≤e) : Γ ⊢[PRAAx]
    multiply (inverseHigh e : PTm n) (highScalar e) ≐ fraction one one := by
  let D : PTm n := coefficient e
  have hD := coefficient_positive (Γ := Γ) e he
  refine (RationalNonnegativePowers.fraction_multiply one D D one hD (le_refl one)).eqTrans ?_
  have hD' : Γ ⊢[PRAAx] le one (D*one) := le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] D ≐ D*one) hD
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hD') (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (fraction_represents _ _ hD') (fraction_represents _ _ (le_refl one)) hD' (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem multiply_sub (w a b : PTm n) :
    Γ ⊢[PRAAx] multiply w (sub a b) ≐ sub (multiply w a) (multiply w b) :=
  (multiply_add _ _ _).eqTrans (add_congr (.eqRefl _) (multiply_negative _ _))

theorem divide_residual (m e : ℕ) (he : 2≤e) (A B M L : PTm n) : Γ ⊢[PRAAx]
    multiply (inverseHigh e) (GaussianStirlingAllOrderPanelPartsOuter.errorSum m e A B M L) ≐
      sub (estimate m e A B M L) (panelPrefix m (e+1) A B M L) := by
  let w := inverseHigh (n := n) e
  let u := panelPrefix m (e+1) A B M L
  let v := sub (multiply (signedMean m) (massPrefix e A B M L)) (panelPrefix (m-1) (e-1) A B M L)
  have hu : Γ ⊢[PRAAx] multiply w (multiply (highScalar e) u) ≐ u :=
    (multiply_associative _ _ _).eqSymm.eqTrans ((multiply_congr (inverse_high_cancel e he) (.eqRefl _)).eqTrans
      ((multiply_commutative _ _).eqTrans (multiply_one_right u (RationalFiniteSum.sum_well_formed _ _ _))))
  exact (multiply_congr (.eqRefl _) (fold_identity m e A B M L)).eqTrans
    ((multiply_sub w (multiply (lowScalar m) v) (multiply (highScalar e) u)).eqTrans
      (add_congr (multiply_associative _ _ _).eqSymm (negative_congr hu)))

theorem embed_sub (a b : PTm n) : Γ ⊢[PRAAx] embed (sub a b) ≐ qsub (embed a) (embed b) :=
  (embed_add a (negative b)).eqTrans (qadd_congr (.eqRefl _) (embed_negative b))

theorem finite_solve_distance (m e : ℕ) (hm : 0<m) (he : 2≤e) (A B M L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    distanceBounded (embed (estimate m e A B M L)) (embed (panelPrefix m (e+1) A B M L))
      (L*errorCoefficient m e (A+B*L) B) M := by
  let w := inverseHigh (n := n) e
  let E := GaussianStirlingAllOrderPanelPartsOuter.errorSum m e A B M L
  have h₁ := finite_outer_recurrence m e hm he A B M L hA hM
  have h₂ := bounded_product _ _ _ _ _ _ (le_refl one) hM (inverse_high_bounded e he) h₁
  have e₁ := (embed_multiply (Γ := Γ) w E).eqSymm.eqTrans (embed_congr (divide_residual m e he A B M L))
  exact bound_congr (e₁.eqTrans (embed_sub _ _)) (one_mul _) (one_mul _) h₂

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsSolve
