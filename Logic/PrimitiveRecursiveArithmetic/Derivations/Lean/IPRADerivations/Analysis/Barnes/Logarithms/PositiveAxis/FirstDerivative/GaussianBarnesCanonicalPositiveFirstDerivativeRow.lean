import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdDerivativePositiveMargin

/-!
# First-to-second logarithmic row expansion on the positive Barnes axis

The ordinary logarithmic derivative of the kept power is its original
base reciprocal. Add the linear correction offset−1 to recover the
same original first-derivative row used in the cofinal tail. At two
positive points, the exact step remainder is bounded by K³H²/(B²k²).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveFirstDerivativeRow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalDerivativeRow (offset)
open GaussianBarnesCanonicalDeflatedFactor (inverseInteger)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalSecondDerivativeStep (step_factor step_bound)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (source step base_lower)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianNameArithmetic (sum_difference)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (canonical canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents
  positive_product qadd qadd_canonical qmul qmul_canonical qzero represents_congr)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum subtract_zero_difference cancel_nested_product)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (bounded distanceBounded qnegative qnegative_canonical qsub qsub_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bounded_product bound_congr qone reciprocal reciprocal_identity)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qadd_sub_cancel qmul_congr qsub_congr qzero_add)
open GaussianReciprocalHorner (qadd_commutative qadd_zero_right qmul_associative qmul_one_right qsub_add_cancel)
open GaussianRootAlgebra (equal equal_of_values sub)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "first" => GaussianBarnesCanonicalDerivativeRow.value
local notation "second" => GaussianBarnesCanonicalSecondDerivativeRow.value

def gain (H K : PTm n) : PTm n := H*H*(K*K*K)

def denominator (B k : PTm n) : PTm n := (B*B)*(k*k)

def remainder (A C B k : PTm n) : PTm n :=
  let i := reciprocal (base (center A B) B k)
  let j := reciprocal (base (center C B) B k)
  let u := qmul (offset (step A C) B k) i
  qmul u (qmul u j)

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (H K : PTm n) :
    Syn.subst σ (gain H K) = gain (Syn.subst σ H) (Syn.subst σ K) := by simp [gain]

theorem fraction_identity (z B k K : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hK : Γ ⊢[PRAAx] le one K) (hz : Γ ⊢[PRAAx] lower (base z B k) one K) :
    Γ ⊢[PRAAx] qsub (qadd (reciprocal (base z B k)) (offset z B k)) qone ≐ first z B k := by
  let w := offset z B k
  let b := base z B k
  let i := reciprocal b
  let u := qmul w w
  let v := first z B k
  let l := qadd qone v
  let r := qadd i w
  have hb : Γ ⊢[PRAAx] canonical b := qadd_canonical _ _
  have nonzero := GaussianNameReciprocal.lower_norm_positive b K hK hz
  have inverse : Γ ⊢[PRAAx] qmul b i ≐ qone := reciprocal_identity b nonzero
  have fold : Γ ⊢[PRAAx] qmul b v ≐ u :=
    (qmul_congr (.eqRefl b) (qmul_commutative u i)).eqTrans
      ((qmul_associative b i u).eqSymm.eqTrans ((qmul_congr inverse (.eqRefl u)).eqTrans
        ((qmul_commutative qone u).eqTrans (qmul_one_right u (qmul_canonical _ _)))))
  have lhs : Γ ⊢[PRAAx] qmul b l ≐ qadd b u :=
    (qmul_add b qone v).eqTrans (qadd_congr (qmul_one_right b hb) fold)
  have hw : Γ ⊢[PRAAx] canonical w := ofGaussian_canonical _ _ (positive_product _ _ hB hk)
  have lin : Γ ⊢[PRAAx] qmul b w ≐ qadd w u :=
    (qmul_commutative b w).eqTrans ((qmul_add w qone w).eqTrans (qadd_congr (qmul_one_right w hw) (.eqRefl u)))
  have rhs : Γ ⊢[PRAAx] qmul b r ≐ qadd b u :=
    (qmul_add b i w).eqTrans ((qadd_congr inverse lin).eqTrans (qadd_associative qone w u).eqSymm)
  have comm := (qmul_commutative i b).eqTrans inverse
  have same : Γ ⊢[PRAAx] r ≐ l :=
    (cancel_nested_product i b r (qadd_canonical _ _) comm).eqSymm.eqTrans
      ((qmul_congr (.eqRefl i) (rhs.eqTrans lhs.eqSymm)).eqTrans
        (cancel_nested_product i b l (qadd_canonical _ _) comm))
  exact (qsub_congr same (.eqRefl qone)).eqTrans (qadd_sub_cancel qone v (qmul_canonical _ _))

theorem offset_difference (A C B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qsub (offset (center C B) B k) (offset (center A B) B k) ≐ offset (step A C) B k := by
  let a := center A B
  let c := center C B
  let h := step A C
  let D := B*k
  have hD := positive_product B k hB hk
  have stepEq : Γ ⊢[PRAAx] equal (sub c a) h := by
    apply equal_of_values <;> simp only [a,c,h,center,step,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat,ZT.toZ_sub] <;>
      (try ipra_simps) <;> ring
  have raw := GaussianRationalMetric.qsub_represents (Γ := Γ) (offset c B k) (offset a B k) c a D hD
    (ofGaussian_represents c D hD) (ofGaussian_represents a D hD)
  exact canonical_unique _ _ h D (qsub_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) stepEq (.eqRefl _) raw) (ofGaussian_represents h D hD)

private theorem affine_cancel (x d u : PTm n) (hx : Γ ⊢[PRAAx] canonical x) :
    Γ ⊢[PRAAx] qsub (qadd x d) (qsub d u) ≐ qadd x u := by
  have insert : Γ ⊢[PRAAx] qadd d (qsub qzero u) ≐ qsub d u :=
    qadd_congr (.eqRefl d) (qzero_add _ (qnegative_canonical u))
  exact (qsub_congr (.eqRefl _) insert.eqSymm).eqTrans
    ((subtract_sum (qadd x d) d (qsub qzero u)).eqSymm.eqTrans
      ((qsub_congr (qsub_add_cancel x d hx) (.eqRefl _)).eqTrans (subtract_zero_difference x u)))

theorem exact_remainder (A C B H K k : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    Γ ⊢[PRAAx] qsub
      (qsub (first (center C B) B (succ k)) (first (center A B) B (succ k)))
      (qmul (ofGaussian (step A C) B) (second (center A B) B (succ k))) ≐ remainder A C B (succ k) := by
  let z := center A B
  let w := center C B
  let n := succ k
  let b := base z B n
  let c := base w B n
  let i := reciprocal b
  let j := reciprocal c
  let d := offset (step A C) B n
  let y := qmul d i
  let u := qmul y i
  let v := qmul y j
  have hb := h.andE₁
  have hn : Γ ⊢[PRAAx] le one n := zero_lt_succ k
  have hK := h.andE₂.andE₂.andE₂.andE₁
  have hl := base_lower A B k K hb hK h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hr := base_lower C B k K hb hK h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have off := offset_difference A C B n hb hn
  have stepEq : Γ ⊢[PRAAx] qsub c b ≐ d :=
    (sum_difference qone qone (offset w B n) (offset z B n)).eqTrans
      ((qadd_congr (GaussianCoefficientNormOrder.qsub_self qone) off).eqTrans
        (qzero_add _ (ofGaussian_canonical _ _ (positive_product _ _ hb hn))))
  have rev : Γ ⊢[PRAAx] qsub i j ≐ v :=
    (GaussianNameReciprocal.inverse_difference b c
      (GaussianNameReciprocal.lower_norm_positive b K hK hl)
      (GaussianNameReciprocal.lower_norm_positive c K hK hr)).eqTrans
        (qmul_congr ((qmul_congr (.eqRefl _) stepEq).eqTrans (qmul_commutative i d)) (.eqRefl _))
  have both :
      Γ ⊢[PRAAx] qsub (first w B n) (first z B n) ≐ qadd (qsub j i) d := by
    let a := qadd j (offset w B n)
    let e := qadd i (offset z B n)
    have cancel : Γ ⊢[PRAAx] qsub (qsub a qone) (qsub e qone) ≐ qsub a e :=
      (sum_difference a e (qnegative qone) (qnegative qone)).eqTrans
        ((qadd_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self (qnegative qone))).eqTrans
          (qadd_zero_right _ (qsub_canonical a e)))
    exact (qsub_congr (fraction_identity w B n K hb hn hK hr).eqSymm (fraction_identity z B n K hb hn hK hl).eqSymm).eqTrans
      (cancel.eqTrans ((sum_difference j i (offset w B n) (offset z B n)).eqTrans (qadd_congr (.eqRefl _) off)))
  have line : Γ ⊢[PRAAx] qmul (ofGaussian (step A C) B) (second z B n) ≐ qsub d u := by
    have rwL : Γ ⊢[PRAAx] qmul (ofGaussian (step A C) B) (second z B n) ≐ qmul d (qsub qone (qmul i i)) :=
      (qmul_associative (ofGaussian (step A C) B) (inverseInteger n) _).eqSymm.eqTrans
        (qmul_congr (step_factor (step A C) B n hb hn) (.eqRefl _))
    exact rwL.eqTrans ((multiplication_difference d qone (qmul i i)).eqSymm.eqTrans
      (qsub_congr (qmul_one_right d (ofGaussian_canonical _ _ (positive_product _ _ hb hn)))
        (qmul_associative d i i).eqSymm))
  have reorder : Γ ⊢[PRAAx] qadd (qsub j i) u ≐ qsub u v :=
    (qadd_commutative (qsub j i) u).eqTrans
      (qadd_congr (.eqRefl _) ((GaussianRationalDistanceOrder.reversed_difference i j).eqSymm.eqTrans
        (GaussianInverseBinomialRows.negative_congr rev)))
  exact (qsub_congr both line).eqTrans
    ((affine_cancel (qsub j i) d u (qsub_canonical _ _)).eqTrans (reorder.eqTrans
      ((multiplication_difference y i j).eqTrans (qmul_congr (.eqRefl _) rev))))

theorem row_error (A C B H K k : PTm n) (h : Γ ⊢[PRAAx] source A C B H K) :
    Γ ⊢[PRAAx] distanceBounded (qsub (first (center C B) B (succ k)) (first (center A B) B (succ k)))
      (qmul (ofGaussian (step A C) B) (second (center A B) B (succ k))) (gain H K) (denominator B (succ k)) := by
  let n := succ k
  let i := reciprocal (base (center A B) B n)
  let j := reciprocal (base (center C B) B n)
  let d := offset (step A C) B n
  let D := B*n
  let u := qmul d i
  have hb := h.andE₁
  have hk : Γ ⊢[PRAAx] le one n := zero_lt_succ k
  have hK := h.andE₂.andE₂.andE₂.andE₁
  have hD := positive_product B n hb hk
  have ho : Γ ⊢[PRAAx] le one (one : PTm _) := le_refl one
  have ib : Γ ⊢[PRAAx] bounded i K one :=
    GaussianRationalLowerBounds.inverse_bound _ one K ho hK
      (base_lower A B k K hb hK h.andE₂.andE₂.andE₂.andE₂.andE₁)
  have jb : Γ ⊢[PRAAx] bounded j K one :=
    GaussianRationalLowerBounds.inverse_bound _ one K ho hK
      (base_lower C B k K hb hK h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁)
  have db : Γ ⊢[PRAAx] bounded d H D := step_bound (step A C) B n H hb hk h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have ub : Γ ⊢[PRAAx] bounded u (H*K) D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product d i H D K one hD ho db ib)
  have vb : Γ ⊢[PRAAx] bounded (qmul u j) (H*K*K) D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product u j (H*K) D K one hD ho ub jb)
  exact bound_congr (exact_remainder A C B H K k h).eqSymm (by unfold gain; ipra_ring)
    (by dsimp only [D,n,denominator]; ipra_ring)
    (bounded_product u (qmul u j) (H*K) D (H*K*K) D hD hD ub vb)

theorem actual_Barnes_positive_first_row_second_derivative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let A := var 0
       let C := var 1
       let B := var 2
       let H := var 3
       let K := var 4
       let k := var 5
       source A C B H K ⟶
         distanceBounded (qsub (first (center C B) B (succ k)) (first (center A B) B (succ k)))
           (qmul (ofGaussian (step A C) B) (second (center A B) B (succ k))) (gain H K) (denominator B (succ k))) :=
  closeUniv 6 (.impI (row_error _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveFirstDerivativeRow
