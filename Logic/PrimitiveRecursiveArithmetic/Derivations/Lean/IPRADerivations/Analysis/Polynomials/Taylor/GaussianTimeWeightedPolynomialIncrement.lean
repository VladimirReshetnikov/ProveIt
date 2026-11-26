import IPRADerivations.Analysis.Polynomials.Taylor.GaussianRationalUniformFirstOrderPolynomial
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# First-order remainder for time times the original polynomial

Multiplying the unchanged polynomial by its rational argument gives
the factor used with the original Euler time power. The original
synthetic slope gives the exact linear term. The uniform quadratic
bound follows from the original polynomial remainder and slope bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianTimeWeightedPolynomialIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (evaluate qadd qmul qzero qmul_canonical canonical positive_product)
open GaussianRationalMetric (qsub bounded)
open GaussianRationalFirstOrderPolynomial (slope remainder)
open GaussianRationalUniformFirstOrderPolynomial (constant slopeConstant)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qadd_sub_cancel qzero_add)
open GaussianRationalPowerDifference (product_difference bounded_sum_same)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalReciprocal (bound_congr bounded_product)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (C t : PTm n) : PTm n := qmul (evaluate C t) t
def linear (C t N : PTm n) : PTm n := qadd (qmul (slope C t N) t) (evaluate C t)
def residual (C t h N : PTm n) : PTm n := qsub (qsub (value C (qadd t h)) (value C t)) (qmul h (linear C t N))
def quadraticBound (C N U : PTm n) : PTm n := U*constant C N U+slopeConstant C N U

theorem residual_identity (C t h N : PTm n) (hh : Γ ⊢[PRAAx] canonical h) :
    Γ ⊢[PRAAx] residual C t h N ≐
      qadd (qmul (remainder C t h N) (qadd t h)) (qmul (qmul h (slope C t N)) h) := by
  let x := evaluate C (qadd t h)
  let y := evaluate C t
  let v := qadd t h
  let D := slope C t N
  let W := qmul h D
  have time : Γ ⊢[PRAAx] qsub v t ≐ h := qadd_sub_cancel t h hh
  have step : Γ ⊢[PRAAx] qsub (value C v) (value C t) ≐ qadd (qmul (qsub x y) v) (qmul y h) :=
    (product_difference x y v t).eqTrans (qadd_congr (.eqRefl _) (qmul_congr (.eqRefl _) time))
  have first : Γ ⊢[PRAAx] qmul h (linear C t N) ≐ qadd (qmul W t) (qmul y h) :=
    (GaussianRationalCoefficientScaling.qmul_add h (qmul D t) y).eqTrans
      (qadd_congr (qmul_associative h D t).eqSymm (qmul_commutative h y))
  have drop : Γ ⊢[PRAAx] qsub (qadd (qmul (qsub x y) v) (qmul y h)) (qadd (qmul W t) (qmul y h)) ≐
      qsub (qmul (qsub x y) v) (qmul W t) := by
    let R := qsub (qmul (qsub x y) v) (qmul W t)
    exact (GaussianNameArithmetic.sum_difference _ _ _ _).eqTrans
      ((qadd_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self (qmul y h))).eqTrans
        ((GaussianRationalLinearProduct.qadd_commutative R qzero).eqTrans
          (qzero_add _ (GaussianRationalMetric.qsub_canonical _ _))))
  exact (qsub_congr step first).eqTrans (drop.eqTrans
    ((product_difference (qsub x y) W v t).eqTrans (qadd_congr (.eqRefl _) (qmul_congr (.eqRefl _) time))))

theorem original_weighted_remainder (C t h N U A B : PTm n) (hlen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hu : Γ ⊢[PRAAx] le one U) (ht : Γ ⊢[PRAAx] bounded t U one)
    (ht' : Γ ⊢[PRAAx] bounded (qadd t h) U one)
    (hb : Γ ⊢[PRAAx] le one B) (hh : Γ ⊢[PRAAx] bounded h A B) (hc : Γ ⊢[PRAAx] canonical h) :
    Γ ⊢[PRAAx] bounded (residual C t h N) (quadraticBound C N U*A*A) (B*B) := by
  let Q := constant C N U
  let S := slopeConstant C N U
  let V := B*B
  let D := slope C t N
  have hs := GaussianRationalUniformFirstOrderPolynomial.slope_bound C t N U hlen hu ht
  have rem := GaussianRationalUniformFirstOrderPolynomial.first_order_bound C t h N U A B hlen hu ht ht' hb hh
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ hb hb
  have low := bounded_product (remainder C t h N) (qadd t h) (Q*A*A) V U one hV (le_refl _) rem ht'
  have left : Γ ⊢[PRAAx] bounded (qmul (remainder C t h N) (qadd t h)) (U*Q*A*A) V :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) low
  have middle := bounded_product h D A B S one hb (le_refl _) hh hs
  have high := bounded_product (qmul h D) h (A*S) (B*one) A B
    (positive_product _ _ hb (le_refl one)) hb middle hh
  have right : Γ ⊢[PRAAx] bounded (qmul (qmul h D) h) (S*A*A) V :=
    bound_congr (.eqRefl _) (by ipra_ring) (by dsimp only [V]; ipra_ring) high
  exact bound_congr (residual_identity C t h N hc).eqSymm
    (by dsimp only [Q,S,quadraticBound]; ipra_ring) (.eqRefl _) (bounded_sum_same _ _ _ _ V hV left right)

theorem original_time_weighted_beta_quadratic_remainder_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 5) ⋏ bounded (var 3) (var 5) one ⋏ bounded (qadd (var 3) (var 4)) (var 5) one ⋏
      le one (var 7) ⋏ bounded (var 4) (var 6) (var 7) ⋏ canonical (var 4)) ⟶
      bounded (residual (GaussianEulerBetaPolynomialPrimitive.primitive (var 0) (var 1) (var 2))
        (var 3) (var 4) (var 2))
        (quadraticBound (GaussianEulerBetaPolynomialPrimitive.primitive (var 0) (var 1) (var 2)) (var 2) (var 5)*var 6*var 6)
        (var 7*var 7)) :=
  closeUniv 8 (.impI (original_weighted_remainder _ _ _ _ _ _ _
    (GaussianEulerBetaPolynomialPrimitive.primitive_length _ _ _) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianTimeWeightedPolynomialIncrement
