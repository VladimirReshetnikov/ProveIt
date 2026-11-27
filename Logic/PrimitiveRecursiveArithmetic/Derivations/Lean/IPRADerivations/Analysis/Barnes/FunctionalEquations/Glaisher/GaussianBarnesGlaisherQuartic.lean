import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherLogarithm
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianIntegerFractionPowers

/-!
# Exact cancellation in the Glaisher increment

After replacing the original logarithm by its fourth Mercator polynomial,
the weighted residual is exactly `(14*N+3)/(144*N^4)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherQuartic

open_ipra
open ComplexLogarithmRemainder (code oneCode zeroCode scale)
open GaussianRootAlgebra (equal equal_of_values equal_re equal_im equal_refl equal_of_code
  re_add im_add re_mul im_mul re_scale im_scale re_neg im_neg re_sub im_sub re_one im_one)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical represents
  represents_congr represents_rescale positive_product qzero qadd qmul qadd_represents qmul_represents
  canonical_unique zero_represents)
open GaussianRationalMetric (qsub qsub_represents qsub_canonical)
open GaussianLocalLogarithmTaylorRemainder (polynomial)
open GaussianFiniteLogarithmPolynomial (coefficient signNumerator sourceTerm value)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "neg" => ComplexLogarithmRemainder.neg
local notation "gadd" => ComplexLogarithmRemainder.add
local notation "gmul" => ComplexLogarithmRemainder.mul

def fourth (N : PTm n) : PTm n := N*N*N*N
def polynomialDenominator (N : PTm n) : PTm n := num 12*fourth N
def polynomialNumerator (N : PTm n) : PTm n :=
  code ⟨num 12*N*N*N+num 4*N, num 6*N*N+num 3⟩ (ZT.ofNat zero)

private theorem polynomial_numerator_re (N : PTm n) :
    ZT.toZ Γ (ComplexLogarithmRemainder.re (polynomialNumerator N)) =
      Groth.ι (Q.mk Γ (num 12*N*N*N+num 4*N)) - Groth.ι (Q.mk Γ (num 6*N*N+num 3)) := by
  rw [polynomialNumerator,ComplexLogarithmRemainder.eval_re_code]
  rfl

private theorem polynomial_numerator_im (N : PTm n) :
    ZT.toZ Γ (ComplexLogarithmRemainder.im (polynomialNumerator N)) = 0 := by
  rw [polynomialNumerator,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat,Q.mk_zero,map_zero]

def weightNumerator (N : PTm n) : PTm n := num 6*N*N+num 6*N+one
def weight (N : PTm n) : PTm n := ofGaussian (scale (weightNumerator N) oneCode) (num 12)
def negativeWeight (N : PTm n) : PTm n := ofGaussian (neg (scale (weightNumerator N) oneCode)) (num 12)
def correction (N : PTm n) : PTm n := ofGaussian (scale (two*N+one) oneCode) (num 4)
def residualNumerator (N : PTm n) : PTm n := num 14*N+num 3
def residualDenominator (N : PTm n) : PTm n := num 144*fourth N
def residual (N : PTm n) : PTm n :=
  ofGaussian (scale (residualNumerator N) oneCode) (residualDenominator N)

theorem fourth_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (fourth N) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _ hN hN) hN) hN

theorem polynomial_denominator_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (polynomialDenominator N) :=
  positive_product _ _ (zero_lt_succ (num 11)) (fourth_positive N hN)

theorem residual_denominator_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (residualDenominator N) :=
  positive_product _ _ (zero_lt_succ (num 143)) (fourth_positive N hN)

private theorem power_one_step (k : PTm n)
    (h : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.power oneCode k) oneCode) :
    Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.power oneCode (succ k)) oneCode := by
  refine GaussianRootAlgebra.equal_trans
    (equal_of_code (ComplexLogarithmRemainder.power_succ oneCode k)) ?_
  apply equal_of_values
  · simp only [re_mul,equal_re h,equal_im h,re_one,im_one]
    ring
  · simp only [im_mul,equal_re h,equal_im h,re_one,im_one]
    ring

private theorem power_one (k : PTm n) :
    Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.power oneCode k) oneCode := by
  have all : Γ ⊢[PRAAx] .all (equal (ComplexLogarithmRemainder.power oneCode (var 0)) oneCode) := by
    ipra_qfind (⟨trivial,trivial⟩) [GaussianRootAlgebra.subst_equal, ComplexLogarithmRemainder.subst_power, ComplexLogarithmRemainder.subst_oneCode]
    · exact
        equal_of_code (ComplexLogarithmRemainder.power_zero (oneCode : PTm n))
    · exact power_one_step (var 0) Prf.hyp0
  simpa only [GaussianRootAlgebra.subst_equal,ComplexLogarithmRemainder.subst_power,
    ComplexLogarithmRemainder.subst_oneCode,Syn.subst_var,Syn.inst_zero] using all.allE k

theorem numeric_power_four (N : PTm n) :
    Γ ⊢[PRAAx] (pw N one ≐ N) ⋏ ((pw N two ≐ N*N) ⋏
      ((pw N (num 3) ≐ N*N*N) ⋏ (pw N (num 4) ≐ fourth N))) := by
  have h1 : Γ ⊢[PRAAx] pw N one ≐ N :=
    (pw_succ N zero).eqTrans ((congrMul (pw_zero N) (.eqRefl _)).eqTrans (one_mul _))
  have h2 : Γ ⊢[PRAAx] pw N two ≐ N*N :=
    (pw_succ N one).eqTrans (congrMul h1 (.eqRefl _))
  have h3 : Γ ⊢[PRAAx] pw N (num 3) ≐ N*N*N :=
    (pw_succ N two).eqTrans (congrMul h2 (.eqRefl _))
  have h4 : Γ ⊢[PRAAx] pw N (num 4) ≐ fourth N :=
    (pw_succ N (num 3)).eqTrans (congrMul h3 (.eqRefl _))
  exact .andI h1 (.andI h2 (.andI h3 h4))

private theorem row_representation (N k c a : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hc : Γ ⊢[PRAAx] (succ k*pw N (succ k))*c ≐ polynomialDenominator N)
    (ha : Γ ⊢[PRAAx] equal (signNumerator k) a) : Γ ⊢[PRAAx]
    represents (inst2 sourceTerm k (ofGaussian oneCode N)) (scale c a) (polynomialDenominator N) := by
  rw [GaussianFiniteLogarithmPolynomial.source_term_at]
  have raw := qmul_represents (coefficient k) (GaussianRationalReciprocal.power (ofGaussian oneCode N) (succ k))
    (signNumerator k) (ComplexLogarithmRemainder.power oneCode (succ k)) (succ k) (pw N (succ k))
    (zero_lt_succ _) (ComplexLogarithmCauchy.power_positive _ _ hN)
    (GaussianFiniteLogarithmPolynomial.coefficient_represents k)
    (GaussianIntegerFractionPowers.power_represents oneCode N (succ k) hN)
  have hv : Γ ⊢[PRAAx] equal (gmul (signNumerator k) (ComplexLogarithmRemainder.power oneCode (succ k))) a := by
    have hp := power_one (Γ := Γ) (succ k)
    apply equal_of_values
    · simp only [re_mul,equal_re ha,equal_re hp,equal_im hp,re_one,im_one]
      ring
    · simp only [im_mul,equal_im ha,equal_re hp,equal_im hp,re_one,im_one]
      ring
  have hr := represents_rescale _ _ _ c (represents_congr (.eqRefl _) hv (.eqRefl _) raw)
  exact represents_congr (.eqRefl _) (equal_refl _) hc hr

private theorem prefix_step (N k a b : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hl : Γ ⊢[PRAAx] represents (value k (ofGaussian oneCode N)) a (polynomialDenominator N))
    (hr : Γ ⊢[PRAAx] represents (inst2 sourceTerm k (ofGaussian oneCode N)) b (polynomialDenominator N)) :
    Γ ⊢[PRAAx] represents (value (succ k) (ofGaussian oneCode N)) (gadd a b) (polynomialDenominator N) :=
  represents_congr (GaussianRationalFiniteSum.sum_succ sourceTerm k (ofGaussian oneCode N)).eqSymm
    (equal_refl _) (.eqRefl _) (qadd_represents _ _ _ _ _ (polynomial_denominator_positive N hN) hl hr)

theorem polynomial_representation (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] represents (polynomial (num 4) oneCode N) (polynomialNumerator N) (polynomialDenominator N) := by
  have hp := numeric_power_four (Γ := Γ) N
  have signs0 := GaussianIntegerFractionPowers.parity_scalar_zero (Γ := Γ) (n := n)
  have signs1 : Γ ⊢[PRAAx] equal (GaussianIntegerFractionPowers.parityScalar one) (neg oneCode) := by
    exact GaussianRootAlgebra.equal_trans
      (GaussianIntegerFractionPowers.parity_scalar_succ zero)
      (by apply equal_of_values <;> simp only [re_neg,im_neg,equal_re signs0,equal_im signs0])
  have signs2 : Γ ⊢[PRAAx] equal (GaussianIntegerFractionPowers.parityScalar two) oneCode := by
    exact GaussianRootAlgebra.equal_trans
      (GaussianIntegerFractionPowers.parity_scalar_succ one)
      (by apply equal_of_values <;> simp only [re_neg,im_neg,equal_re signs1,equal_im signs1,neg_neg])
  have signs3 : Γ ⊢[PRAAx] equal (GaussianIntegerFractionPowers.parityScalar (num 3)) (neg oneCode) := by
    exact GaussianRootAlgebra.equal_trans
      (GaussianIntegerFractionPowers.parity_scalar_succ two)
      (by apply equal_of_values <;> simp only [re_neg,im_neg,equal_re signs2,equal_im signs2])
  have base := represents_congr (GaussianRationalFiniteSum.sum_zero (Γ := Γ) sourceTerm (ofGaussian oneCode N)).eqSymm
    (equal_refl zeroCode) (.eqRefl _) (zero_represents (polynomialDenominator N))
  have r1 := row_representation N zero (num 12*N*N*N) oneCode hN
    ((congrMul (congrMul (.eqRefl one) hp.andE₁) (.eqRefl _)).eqTrans (by unfold polynomialDenominator fourth; ipra_ring)) signs0
  have r2 := row_representation N one (num 6*N*N) (neg oneCode) hN
    ((congrMul (congrMul (.eqRefl two) hp.andE₂.andE₁) (.eqRefl _)).eqTrans
      (by unfold polynomialDenominator fourth; ipra_ring)) signs1
  have r3 := row_representation N two (num 4*N) oneCode hN
    ((congrMul (congrMul (.eqRefl (num 3)) hp.andE₂.andE₂.andE₁) (.eqRefl _)).eqTrans
      (by unfold polynomialDenominator fourth; ipra_ring)) signs2
  have r4 := row_representation N (num 3) (num 3) (neg oneCode) hN
    ((congrMul (congrMul (.eqRefl (num 4)) hp.andE₂.andE₂.andE₂) (.eqRefl _)).eqTrans
      (by unfold polynomialDenominator fourth; ipra_ring)) signs3
  have p1 := prefix_step N zero _ _ hN base r1
  have p2 := prefix_step N one _ _ hN p1 r2
  have p3 := prefix_step N two _ _ hN p2 r3
  have p4 := prefix_step N (num 3) _ _ hN p3 r4
  let v := gadd (gadd (gadd (gadd zeroCode (scale (num 12*N*N*N) oneCode))
    (scale (num 6*N*N) (neg oneCode))) (scale (num 4*N) oneCode)) (scale (num 3) (neg oneCode))
  have eq : Γ ⊢[PRAAx] equal v (polynomialNumerator N) := by
    apply equal_of_values
    · simp only [v,re_add,re_scale,re_neg,re_one,GaussianRootAlgebra.re_zero,polynomial_numerator_re]
      ipra_simps
      ring
    · simp only [v,im_add,im_scale,im_neg,im_one,GaussianRootAlgebra.im_zero,polynomial_numerator_im]
      ring
  exact represents_congr (.eqRefl _) eq (.eqRefl _) p4

theorem exact_cancellation (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qsub (correction N) (qmul (weight N) (polynomial (num 4) oneCode N)) ≐ residual N := by
  have hd := residual_denominator_positive N hN
  have hw := ofGaussian_represents (Γ := Γ) (scale (weightNumerator N) oneCode) (num 12) (zero_lt_succ (num 11))
  have hq := qmul_represents _ _ _ _ _ _ (zero_lt_succ (num 11)) (polynomial_denominator_positive N hN)
    hw (polynomial_representation N hN)
  have correctionRep := represents_rescale _ _ _ (num 36*fourth N)
    (ofGaussian_represents (Γ := Γ) (scale (two*N+one) oneCode) (num 4) (zero_lt_succ (num 3)))
  have eU : Γ ⊢[PRAAx] num 4*(num 36*fourth N) ≐ residualDenominator N := by
    unfold residualDenominator
    ipra_ring
  have hu := represents_congr (.eqRefl _) (equal_refl _) eU correctionRep
  have eV : Γ ⊢[PRAAx] num 12*polynomialDenominator N ≐ residualDenominator N := by
    unfold polynomialDenominator residualDenominator
    ipra_ring
  have hv := represents_congr (.eqRefl _) (equal_refl _) eV hq
  have raw := qsub_represents _ _ _ _ (residualDenominator N) hd hu hv
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (GaussianRootAlgebra.sub (scale (num 36*fourth N) (scale (two*N+one) oneCode))
        (gmul (scale (weightNumerator N) oneCode) (polynomialNumerator N)))
      (scale (residualNumerator N) oneCode) := by
    apply equal_of_values
    · simp only [re_sub,re_scale,re_mul,im_scale,re_one,im_one,polynomial_numerator_re,polynomial_numerator_im,
        residualNumerator,weightNumerator,fourth]
      ipra_simps
      ring
    · simp only [im_sub,im_scale,im_mul,re_scale,re_one,im_one,polynomial_numerator_re,polynomial_numerator_im]
      ring
  exact canonical_unique _ _ _ (residualDenominator N) (qsub_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) eq (.eqRefl _) raw) (ofGaussian_represents _ _ hd)

theorem actual_Glaisher_quartic_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ qsub (correction (var 0)) (qmul (weight (var 0)) (polynomial (num 4) oneCode (var 0))) ≐ residual (var 0)) :=
  closeUniv 1 (.impI (exact_cancellation _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherQuartic
