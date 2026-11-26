import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeRow
import IPRADerivations.Analysis.Barnes.Deflation.GaussianBarnesCanonicalDeflatedFactor

/-!
# Original rational second derivative of a retained Barnes log row

The row uses the original base reciprocal. The two formulas for its
second derivative agree as exact rational Gaussian values. The disk
guard gives the paper's uniform twelve-times-radius bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeRow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode normSq_one)
open GaussianBarnesCanonicalDeflatedFactor (inverseInteger)
open GaussianBarnesCanonicalDerivativeRow (offset offset_bound base_lower inverse_base_bound)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalLogRow (source)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents qadd qmul qmul_canonical positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalPowerDifference (bounded_sum_same product_difference)
open GaussianRationalReciprocal (qone qone_bounded reciprocal reciprocal_identity reciprocal_canonical bounded_product bound_congr)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qone_canonical qadd_congr qsub_congr qmul_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qmul_associative qmul_one_right qadd_commutative)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseSquare (z B k : PTm n) : PTm n :=
  qmul (reciprocal (base z B k)) (reciprocal (base z B k))

def value (z B k : PTm n) : PTm n := qmul (inverseInteger k) (qsub qone (inverseSquare z B k))

def expanded (z B k : PTm n) : PTm n :=
  qmul (inverseInteger k)
    (qmul (qmul (offset z B k) (qadd (qadd qone qone) (offset z B k))) (inverseSquare z B k))

def boundNumerator (R : PTm n) : PTm n := num 12*R
abbrev boundDenominator (k : PTm n) : PTm n := GaussianBarnesCanonicalDerivativeRow.boundDenominator k

@[simp] theorem subst_inverseSquare {m : ℕ} (σ : Fin n → PTm m) (z B k : PTm n) :
    Syn.subst σ (inverseSquare z B k) = inverseSquare (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [inverseSquare]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (z B k : PTm n) :
    Syn.subst σ (value z B k) = value (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [value,inverseInteger,oneCode,one]

@[simp] theorem subst_expanded {m : ℕ} (σ : Fin n → PTm m) (z B k : PTm n) :
    Syn.subst σ (expanded z B k) = expanded (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [expanded,inverseInteger,oneCode,one]

@[simp] theorem subst_boundNumerator {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (boundNumerator R) = boundNumerator (Syn.subst σ R) := by simp [boundNumerator]

theorem reciprocal_base (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] qmul (base z B k) (reciprocal (base z B k)) ≐ qone :=
  reciprocal_identity _ (GaussianNameReciprocal.lower_norm_positive _ two (zero_lt_succ one) (base_lower z R B k h))

private theorem exchange_products (a b c d : PTm n) :
    Γ ⊢[PRAAx] qmul (qmul a b) (qmul c d) ≐ qmul (qmul a c) (qmul b d) := by
  have middle := (qmul_associative (Γ := Γ) b c d).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative b c) (.eqRefl d)).eqTrans (qmul_associative c b d))
  exact (qmul_associative a b (qmul c d)).eqTrans
    ((qmul_congr (.eqRefl a) middle).eqTrans (qmul_associative a c (qmul b d)).eqSymm)

private theorem base_square_minus_one (w : PTm n) (hw : Γ ⊢[PRAAx] GaussianRationalHorner.canonical w) :
    Γ ⊢[PRAAx] qsub (qmul (qadd qone w) (qadd qone w)) qone ≐ qmul w (qadd (qadd qone qone) w) := by
  let b := qadd qone w
  have one := qmul_one_right (Γ := Γ) qone qone_canonical
  have moved := (qsub_congr (.eqRefl (qmul b b)) one.eqSymm).eqTrans (product_difference b qone b qone)
  have cancel := qadd_sub_cancel qone w hw
  have joined := moved.eqTrans (qadd_congr (qmul_congr cancel (.eqRefl b))
    ((qmul_congr (.eqRefl qone) cancel).eqTrans (qmul_commutative qone w)))
  have pair : Γ ⊢[PRAAx] qadd (qmul w b) (qmul w qone) ≐ qmul w (qadd b qone) := (qmul_add w b qone).eqSymm
  have orient : Γ ⊢[PRAAx] qadd b qone ≐ qadd (qadd qone qone) w :=
    (qadd_commutative b qone).eqTrans (qadd_associative qone qone w).eqSymm
  exact joined.eqTrans (pair.eqTrans (qmul_congr (.eqRefl w) orient))

theorem expanded_formula (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] value z B k ≐ expanded z B k := by
  let b := base z B k
  let w := offset z B k
  let i := reciprocal b
  let j := inverseSquare z B k
  have wd : Γ ⊢[PRAAx] le one (B*k) := positive_product _ _ h.andE₁ h.andE₂.andE₁
  have hw : Γ ⊢[PRAAx] GaussianRationalHorner.canonical w := ofGaussian_canonical _ _ wd
  have inv := reciprocal_base z R B k h
  have product : Γ ⊢[PRAAx] qmul j (qmul b b) ≐ qone :=
    (qmul_commutative j (qmul b b)).eqTrans
      ((exchange_products b b i i).eqTrans
        ((qmul_congr inv inv).eqTrans (qmul_one_right qone qone_canonical)))
  have attach : Γ ⊢[PRAAx] qmul j (qsub (qmul b b) qone) ≐ qsub qone j :=
    (multiplication_difference j (qmul b b) qone).eqSymm.eqTrans
      (qsub_congr product (qmul_one_right j (qmul_canonical i i)))
  have restore := attach.eqSymm.eqTrans
    ((qmul_congr (.eqRefl j) (base_square_minus_one w hw)).eqTrans (qmul_commutative _ _))
  exact qmul_congr (.eqRefl (inverseInteger k)) restore

theorem inverse_integer_bound (k : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] bounded (inverseInteger k) one k :=
  bounded_of_cleared _ _ _ _ _ hk hk (ofGaussian_represents oneCode k hk)
    (le_congr (congrMul (.eqRefl (k*k)) normSq_one).eqSymm (by ipra_ring) (le_refl (k*k*one)))

private theorem offset_unit_bound (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (offset z B k) one one := by
  have grow : Γ ⊢[PRAAx] le R (two*R) :=
    le_congr (one_mul R) (.eqRefl _) (mul_le_mul_right R (zero_lt_succ one))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ h.andE₂.andE₁ (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) (le_trans grow h.andE₂.andE₂.andE₂)) (offset_bound z R B k h)

theorem row_bound (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (value z B k) (boundNumerator R) (boundDenominator k) := by
  let w := offset z B k
  let i := reciprocal (base z B k)
  let u := qadd (qadd qone qone) w
  let j := inverseSquare z B k
  let v := qmul w u
  have hk := h.andE₂.andE₁
  have ho : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl one
  have unit := offset_unit_bound z R B k h
  have first := bounded_sum_same qone qone one one one ho qone_bounded qone_bounded
  have hu := bounded_sum_same (qadd qone qone) w (one+one) one one ho first unit
  have hv := bounded_product w u R k (one+one+one) one hk ho (offset_bound z R B k h) hu
  have inverse := inverse_base_bound z R B k h
  have hj : Γ ⊢[PRAAx] bounded j (two*two) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul one) (bounded_product i i two one two one ho ho inverse inverse)
  have hinner := bounded_product v j (R*(one+one+one)) (k*one) (two*two) one
    (positive_product _ _ hk ho) ho hv hj
  have prod := bounded_product (inverseInteger k) (qmul v j) one k _ _ hk
    (positive_product _ _ (positive_product _ _ hk ho) ho) (inverse_integer_bound k hk) hinner
  exact bound_congr (expanded_formula z R B k h).eqSymm (by unfold boundNumerator; ipra_ring) (by change Γ ⊢[PRAAx] k*(k*one*one) ≐ k*k; ipra_ring) prod

theorem actual_Barnes_second_derivative_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let k := var 3
     source z R B k ⟶
       (value z B k ≐ expanded z B k ⋏ bounded (value z B k) (boundNumerator R) (boundDenominator k))) :=
  closeUniv 4 (.impI (.andI (expanded_formula _ _ _ _ Prf.hyp0) (row_bound _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeRow
