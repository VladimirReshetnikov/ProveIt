import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalSecondDerivativeRow
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalHeadCorrectionDerivative
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalInverseQuadraticAlgebra

/-!
# Second derivative of the original Barnes first-derivative row

The exact resolvent difference expresses the remainder as a product
of two copies of the original offset displacement and three original
base reciprocals. Both endpoints use the retained half-disk guards.
The resultant quadratic bound is summable in the row index.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeStep

open_ipra
open ComplexLogarithmRemainder (add mul oneCode)
open GaussianBarnesCanonicalDeflatedFactor (inverseInteger)
open GaussianBarnesCanonicalDerivativeRow (offset base_lower fraction_identity inverse_base_bound)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalSecondDerivativeRow (inverseSquare)
open GaussianNameArithmetic (sum_difference)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents qadd qmul qzero
  qmul_canonical positive_product qmul_represents canonical_unique represents_congr)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum subtract_zero_difference)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub qsub_canonical qnegative qnegative_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone reciprocal bounded_product bound_congr)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qsub_congr qadd_congr qmul_congr qzero_add)
open GaussianReciprocalHorner (qmul_associative qmul_one_right qadd_commutative qadd_zero_right qsub_add_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rowSource" => GaussianBarnesCanonicalLogRow.source
local notation "first" => GaussianBarnesCanonicalDerivativeRow.value
local notation "second" => GaussianBarnesCanonicalSecondDerivativeRow.value
local notation "nativeBound" => ComplexLogarithmRemainder.bounded
local notation "self_sub" => GaussianCoefficientNormOrder.qsub_self
local notation "sub_zero_right" => GaussianRationalReconstruction.qsub_zero_right

def source (z h R B k H : PTm n) : Fm PTm n :=
  rowSource z R B k ⋏ (rowSource (add z h) R B k ⋏ nativeBound h H)

def increment (z h B k : PTm n) : PTm n := qsub (first (add z h) B k) (first z B k)
def linear (z h B k : PTm n) : PTm n := qmul (ofGaussian h B) (second z B k)
def scaledOffset (z h B k : PTm n) : PTm n := qmul (offset h B k) (reciprocal (base z B k))
def remainder (z h B k : PTm n) : PTm n :=
  qmul (scaledOffset z h B k) (qmul (scaledOffset z h B k) (reciprocal (base (add z h) B k)))

def errorNumerator (H : PTm n) : PTm n := num 8*H*H
def errorDenominator (B k : PTm n) : PTm n := (B*B)*(k*k)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z h R B k H : PTm n) :
    (source z h R B k H).subst σ =
      source (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) :=
  by simp [source]

@[simp] theorem subst_increment {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (increment z h B k) = increment (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [increment]

@[simp] theorem subst_linear {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (linear z h B k) = linear (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [linear]

@[simp] theorem subst_scaledOffset {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (scaledOffset z h B k) = scaledOffset (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [scaledOffset]

@[simp] theorem subst_remainder {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (remainder z h B k) = remainder (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [remainder]

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (H : PTm n) :
    Syn.subst σ (errorNumerator H) = errorNumerator (Syn.subst σ H) := by simp [errorNumerator]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (B k : PTm n) :
    Syn.subst σ (errorDenominator B k) = errorDenominator (Syn.subst σ B) (Syn.subst σ k) := by simp [errorDenominator]

theorem step_factor (h B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qmul (ofGaussian h B) (inverseInteger k) ≐ offset h B k := by
  have hd := positive_product B k hB hk
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (mul h oneCode) h := by
    apply GaussianRootAlgebra.equal_of_values <;> simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring
  have r := qmul_represents (ofGaussian h B) (inverseInteger k) h oneCode B k hB hk
    (ofGaussian_represents h B hB) (ofGaussian_represents oneCode k hk)
  exact canonical_unique _ _ h (B*k) (qmul_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) e (.eqRefl _) r) (ofGaussian_represents h (B*k) hd)

private theorem offset_difference (z h B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qsub (offset (add z h) B k) (offset z B k) ≐ offset h B k :=
  GaussianBarnesCanonicalHeadCorrectionDerivative.point_increment z h (B*k) (positive_product B k hB hk)

theorem base_difference (z h B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qsub (base (add z h) B k) (base z B k) ≐ offset h B k :=
  (sum_difference qone qone (offset (add z h) B k) (offset z B k)).eqTrans
    ((qadd_congr (self_sub qone) (offset_difference z h B k hB hk)).eqTrans
      (qzero_add _ (ofGaussian_canonical _ _ (positive_product _ _ hB hk))))

private theorem affine_cancel (x u v : PTm n) (hx : Γ ⊢[PRAAx] GaussianRationalHorner.canonical x) : Γ ⊢[PRAAx]
    qsub (qadd x u) (qsub u v) ≐ qadd x v := by
  have insert : Γ ⊢[PRAAx] qadd u (qsub qzero v) ≐ qsub u v :=
    qadd_congr (.eqRefl u) (qzero_add _ (qnegative_canonical v))
  exact (qsub_congr (.eqRefl _) insert.eqSymm).eqTrans
    ((subtract_sum (qadd x u) u (qsub qzero v)).eqSymm.eqTrans
      ((qsub_congr (qsub_add_cancel x u hx) (.eqRefl _)).eqTrans (subtract_zero_difference x v)))

private theorem difference_cancel (a b : PTm n) : Γ ⊢[PRAAx] qadd (qsub a b) (qsub b a) ≐ qzero :=
  (sum_difference a b b a).eqSymm.eqTrans
    ((qsub_congr (qadd_commutative a b) (.eqRefl _)).eqTrans (self_sub _))

private theorem resolvent_residual (i j d : PTm n) (hd : Γ ⊢[PRAAx] GaussianRationalHorner.canonical d)
    (e : Γ ⊢[PRAAx] qsub i j ≐ qmul (qmul d i) j) :
    Γ ⊢[PRAAx] qsub (qadd (qsub j i) d) (qmul d (qsub qone (qmul i i))) ≐
      qmul (qmul d i) (qmul (qmul d i) j) := by
  let Y := qmul d i
  let U := qmul Y i
  let V := qmul Y j
  let W := qsub j i
  have line : Γ ⊢[PRAAx] qmul d (qsub qone (qmul i i)) ≐ qsub d U :=
    (multiplication_difference d qone (qmul i i)).eqSymm.eqTrans
      (qsub_congr (qmul_one_right d hd) (qmul_associative d i i).eqSymm)
  have cancel : Γ ⊢[PRAAx] qadd W V ≐ qzero :=
    (qadd_congr (.eqRefl _) e.eqSymm).eqTrans (difference_cancel j i)
  have reduce : Γ ⊢[PRAAx] qadd W U ≐ qsub U V := by
    have zeroed : Γ ⊢[PRAAx] qadd W U ≐ qsub (qadd W U) qzero :=
      (sub_zero_right (qadd W U) (GaussianRationalHorner.qadd_canonical _ _)).eqSymm
    exact zeroed.eqTrans ((qsub_congr (.eqRefl _) cancel.eqSymm).eqTrans
      ((sum_difference W W U V).eqTrans
        ((qadd_congr (self_sub W) (.eqRefl _)).eqTrans (qzero_add _ (qsub_canonical U V)))))
  exact (qsub_congr (.eqRefl _) line).eqTrans
    ((affine_cancel W d U (qsub_canonical j i)).eqTrans
      (reduce.eqTrans ((multiplication_difference Y i j).eqTrans (qmul_congr (.eqRefl _) e))))

theorem exact_remainder (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] qsub (increment z h B k) (linear z h B k) ≐ remainder z h B k := by
  let w := add z h
  let b := base z B k
  let c := base w B k
  let i := reciprocal b
  let j := reciprocal c
  let d := offset h B k
  let u := offset z B k
  let v := offset w B k
  let p := qadd i u
  let q := qadd j v
  have hz := hs.andE₁
  have hw := hs.andE₂.andE₁
  have hB := hz.andE₁
  have hk := hz.andE₂.andE₁
  have hd := positive_product _ _ hB hk
  have nz := GaussianNameReciprocal.lower_norm_positive b two (zero_lt_succ one) (base_lower z R B k hz)
  have nw := GaussianNameReciprocal.lower_norm_positive c two (zero_lt_succ one) (base_lower w R B k hw)
  have rev : Γ ⊢[PRAAx] qsub i j ≐ qmul (qmul d i) j :=
    (GaussianNameReciprocal.inverse_difference b c nz nw).eqTrans
      (qmul_congr ((qmul_congr (.eqRefl i) (base_difference z h B k hB hk)).eqTrans (qmul_commutative i d)) (.eqRefl j))
  have part : Γ ⊢[PRAAx] increment z h B k ≐ qadd (qsub j i) d := by
    refine (qsub_congr (fraction_identity w R B k hw).eqSymm (fraction_identity z R B k hz).eqSymm).eqTrans ?_
    have cancel : Γ ⊢[PRAAx] qsub (qsub q qone) (qsub p qone) ≐ qsub q p :=
      (sum_difference q p (qnegative qone) (qnegative qone)).eqTrans
        ((qadd_congr (.eqRefl _) (self_sub (qnegative qone))).eqTrans (qadd_zero_right _ (qsub_canonical q p)))
    exact cancel.eqTrans ((sum_difference j i v u).eqTrans (qadd_congr (.eqRefl _) (offset_difference z h B k hB hk)))
  have line : Γ ⊢[PRAAx] linear z h B k ≐ qmul d (qsub qone (qmul i i)) :=
    (qmul_associative (ofGaussian h B) (inverseInteger k) (qsub qone (inverseSquare z B k))).eqSymm.eqTrans
      (qmul_congr (step_factor h B k hB hk) (.eqRefl _))
  exact (qsub_congr part line).eqTrans (resolvent_residual i j d (ofGaussian_canonical _ _ hd) rev)

theorem step_bound (h B k H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k)
    (hh : Γ ⊢[PRAAx] nativeBound h H) : Γ ⊢[PRAAx] bounded (offset h B k) H (B*k) := by
  let D := B*k
  have hD := positive_product _ _ hB hk
  exact bounded_of_cleared _ _ _ _ _ hD hD (ofGaussian_represents _ _ hD)
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (D*D) hh))

theorem quadratic_bound (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] distanceBounded (increment z h B k) (linear z h B k) (errorNumerator H) (errorDenominator B k) := by
  let w := add z h
  let i := reciprocal (base z B k)
  let j := reciprocal (base w B k)
  let d := offset h B k
  let D := B*k
  let Y := scaledOffset z h B k
  have hz := hs.andE₁
  have hw := hs.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hz.andE₁ hz.andE₂.andE₁
  have ho : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl one
  have db : Γ ⊢[PRAAx] bounded d H D := step_bound h B k H hz.andE₁ hz.andE₂.andE₁ hs.andE₂.andE₂
  have ib : Γ ⊢[PRAAx] bounded i two one := inverse_base_bound z R B k hz
  have jb : Γ ⊢[PRAAx] bounded j two one := inverse_base_bound w R B k hw
  have yi : Γ ⊢[PRAAx] bounded Y (H*two) D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product d i H D two one hD ho db ib)
  have vv : Γ ⊢[PRAAx] bounded (qmul Y j) (H*two*two) D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product Y j (H*two) D two one hD ho yi jb)
  have prod := bounded_product Y (qmul Y j) (H*two) D (H*two*two) D hD hD yi vv
  exact bound_congr (exact_remainder z h R B k H hs).eqSymm (by unfold errorNumerator; ipra_ring)
    (by dsimp only [D,errorDenominator]; ipra_ring) prod

theorem actual_Barnes_first_derivative_row_second_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let k := var 4
     let H := var 5
     source z h R B k H ⟶
       (qsub (increment z h B k) (linear z h B k) ≐ remainder z h B k ⋏
         distanceBounded (increment z h B k) (linear z h B k) (errorNumerator H) (errorDenominator B k))) :=
  closeUniv 6 (.impI (.andI (exact_remainder _ _ _ _ _ _ Prf.hyp0) (quadratic_bound _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeStep
