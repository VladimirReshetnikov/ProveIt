import IPRADerivations.Analysis.Barnes.Logarithms.FiniteRows.GaussianBarnesCanonicalLogRow
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalBase
import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaLocalPoleGuards
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# Rational first-derivative row of the Barnes canonical logarithm

For the original factor base `1+w`, with `w=z/(B*k)`, the canonical
derivative expression is `w²/(1+w)`. The half-disk guard keeps the
actual reciprocal within two, giving the literal bound `2R²/k²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeRow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalLogRow (source)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaLocalPoleGuards (center translated_pole_right)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qadd qadd_canonical qmul qmul_canonical)
open GaussianRationalLowerBounds (lower lower_from_representation inverse_bound)
open GaussianRationalMetric (bounded bounded_of_cleared qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_identity bounded_product)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRootAlgebra (equal equal_of_values normSq_equal re_add im_add re_neg im_neg
  re_scale im_scale re_one im_one)
open GaussianRationalReciprocal (qone)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def offset (z B k : PTm n) : PTm n := ofGaussian z (B*k)
def value (z B k : PTm n) : PTm n := qmul (qmul (offset z B k) (offset z B k)) (reciprocal (base z B k))
def boundNumerator (R : PTm n) : PTm n := two*(R*R)
def boundDenominator (k : PTm n) : PTm n := k*k

@[simp] theorem subst_offset {m : ℕ} (σ : Fin n → PTm m) (z B k : PTm n) :
    Syn.subst σ (offset z B k) = offset (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) := by simp [offset]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (z B k : PTm n) :
    Syn.subst σ (value z B k) = value (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) := by simp [value]

@[simp] theorem subst_boundNumerator {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (boundNumerator R) = boundNumerator (Syn.subst σ R) := by simp [boundNumerator,two]

@[simp] theorem subst_boundDenominator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (boundDenominator k) = boundDenominator (Syn.subst σ k) := by simp [boundDenominator]

theorem bound_denominator_positive (k : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] le one (boundDenominator k) :=
  positive_product _ _ hk hk

theorem offset_bound (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (offset z B k) R k := by
  let d := B*k
  have hk := h.andE₂.andE₁
  have hd := positive_product B k h.andE₁ hk
  have hz := h.andE₂.andE₂.andE₁
  change Γ ⊢[PRAAx] le (normSq z) ((R*B)*(R*B)) at hz
  exact bounded_of_cleared _ _ _ _ _ hd hk (ofGaussian_represents z d hd)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (k*k) hz))

private theorem translated_at_unit (z B k : PTm n) :
    Γ ⊢[PRAAx] equal (translated (center z (B*k) zero) (B*k) one) (translated z B k) := by
  apply equal_of_values <;>
    simp only [translated,center,GaussianGammaPoleZeros.poleNumerator,re_add,im_add,re_neg,im_neg,
      re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

theorem base_lower (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] lower (base z B k) one two := by
  let d := B*k
  let a := translated z B k
  have hk := h.andE₂.andE₁
  have hd := positive_product B k h.andE₁ hk
  have h2 : Γ ⊢[PRAAx] le one two := zero_lt_succ one
  have fit : Γ ⊢[PRAAx] le (two*(R*B)) (one*d) :=
    le_congr (by ipra_ring) (by dsimp only [d]; ipra_ring) (mul_le_mul_right B h.andE₂.andE₂.andE₂)
  have scaled := ComplexLogarithmRemainder.bounded_scale two h.andE₂.andE₂.andE₁
  have disk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (ComplexLogarithmRemainder.scale two z) (one*d) :=
    le_trans scaled (le_mul_mono fit fit)
  have geo := translated_pole_right z d one one two zero one (le_congr (by ipra_ring) (.eqRefl _) (le_refl two))
    disk (zero_lt_succ zero)
  change Γ ⊢[PRAAx] le ((one*d)*(one*d)) (two*two*normSq (translated (center z d zero) d one)) at geo
  have clear : Γ ⊢[PRAAx] le (one*one*(d*d)) (two*two*normSq a) :=
    le_congr (by ipra_ring) (congrMul (.eqRefl _) (normSq_equal (translated_at_unit z B k))) geo
  exact lower_from_representation (base z B k) a d one two hd h2
    (GaussianBarnesCanonicalBase.base_represents z B k h.andE₁ hk) clear

theorem inverse_base_bound (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (reciprocal (base z B k)) two one :=
  inverse_bound _ one two (le_refl one) (zero_lt_succ one) (base_lower z R B k h)

theorem row_bound (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (value z B k) (boundNumerator R) (boundDenominator k) := by
  let w := offset z B k
  let d := boundDenominator k
  let i := reciprocal (base z B k)
  have hk := h.andE₂.andE₁
  have hd := bound_denominator_positive k hk
  have disk := offset_bound z R B k h
  have square : Γ ⊢[PRAAx] bounded (qmul w w) (R*R) d :=
    bounded_product w w R k R k hk hk disk disk
  have product := bounded_product (qmul w w) i (R*R) d two one hd (le_refl one) square (inverse_base_bound z R B k h)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (mul_comm _ _) (by ipra_ring) product

theorem fraction_identity (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] qsub (qadd (reciprocal (base z B k)) (offset z B k)) qone ≐ value z B k := by
  let w := offset z B k
  let b := base z B k
  let i := reciprocal b
  let u := qmul w w
  let v := value z B k
  let l := qadd qone v
  let r := qadd i w
  have hb : Γ ⊢[PRAAx] GaussianRationalHorner.canonical b := qadd_canonical _ _
  have nonzero := GaussianNameReciprocal.lower_norm_positive b two (zero_lt_succ one) (base_lower z R B k h)
  have inverse : Γ ⊢[PRAAx] qmul b i ≐ qone := reciprocal_identity b nonzero
  have one_mul (a : PTm n) (ha : Γ ⊢[PRAAx] GaussianRationalHorner.canonical a) :
      Γ ⊢[PRAAx] qmul qone a ≐ a :=
    (qmul_commutative qone a).eqTrans (qmul_one_right a ha)
  have fold : Γ ⊢[PRAAx] qmul b v ≐ u :=
    (qmul_congr (.eqRefl b) (qmul_commutative u i)).eqTrans
      ((qmul_associative b i u).eqSymm.eqTrans
        ((qmul_congr inverse (.eqRefl u)).eqTrans (one_mul u (qmul_canonical _ _))))
  have lhs : Γ ⊢[PRAAx] qmul b l ≐ qadd b u :=
    (qmul_add b qone v).eqTrans (qadd_congr (qmul_one_right b hb) fold)
  have hw : Γ ⊢[PRAAx] GaussianRationalHorner.canonical w :=
    GaussianRationalHorner.ofGaussian_canonical _ _ (positive_product _ _ h.andE₁ h.andE₂.andE₁)
  have lin : Γ ⊢[PRAAx] qmul b w ≐ qadd w u :=
    (qmul_commutative b w).eqTrans ((qmul_add w qone w).eqTrans
      (qadd_congr (qmul_one_right w hw) (.eqRefl u)))
  have rhs : Γ ⊢[PRAAx] qmul b r ≐ qadd b u :=
    (qmul_add b i w).eqTrans ((qadd_congr inverse lin).eqTrans (qadd_associative qone w u).eqSymm)
  have commute := (qmul_commutative i b).eqTrans inverse
  have release (a : PTm n) (ha : Γ ⊢[PRAAx] GaussianRationalHorner.canonical a) :
      Γ ⊢[PRAAx] qmul i (qmul b a) ≐ a :=
    (qmul_associative i b a).eqSymm.eqTrans ((qmul_congr commute (.eqRefl a)).eqTrans (one_mul a ha))
  have same : Γ ⊢[PRAAx] r ≐ l :=
    (release r (qadd_canonical _ _)).eqSymm.eqTrans
      ((qmul_congr (.eqRefl i) (rhs.eqTrans lhs.eqSymm)).eqTrans (release l (qadd_canonical _ _)))
  exact (qsub_congr same (.eqRefl qone)).eqTrans (qadd_sub_cancel qone v (qmul_canonical _ _))

theorem actual_Barnes_first_derivative_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (value (var 0) (var 2) (var 3)) (boundNumerator (var 1)) (boundDenominator (var 3))) :=
  closeUniv 4 (.impI (row_bound _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeRow
