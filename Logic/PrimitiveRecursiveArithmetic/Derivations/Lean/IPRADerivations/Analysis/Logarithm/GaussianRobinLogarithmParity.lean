import IPRADerivations.Analysis.Logarithm.GaussianRobinOddLogarithm
import IPRADerivations.Analysis.Logarithm.GaussianFiniteLogarithmPolynomial
import IPRADerivations.Analysis.RationalArithmetic.GaussianIntegerFractionPowers
import IPRADerivations.Analysis.Names.GaussianNameArithmetic

/-!
# Finite logarithm parity at the original Robin cutoff

Subtracting the two actual truncated logarithms at opposite real
arguments cancels the even powers and doubles the odd powers. At
degree `2K` the result is exactly the normalized lower Robin series
with `K` odd terms.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRobinLogarithmParity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRobinOddLogarithm (oddIndex oddSum term)
open GaussianFiniteLogarithmPolynomial (coefficient coefficient_represents sourceTerm source_term_at value)
open GaussianRationalHorner
  (qzero qadd qmul canonical represents ofGaussian ofGaussian_represents positive_product represents_congr canonical_unique qmul_represents)
open GaussianRationalSyntheticDivision (qzero_canonical qzero_add qmul_congr qadd_congr qsub_congr)
open GaussianRationalMetric (qsub qsub_represents)
open GaussianRootAlgebra
  (equal equal_of_values equal_symm equal_re equal_im values_of_code re_one im_one re_zero im_zero
    re_scale im_scale re_mul im_mul re_neg im_neg re_sub im_sub)
open ComplexLogarithmRemainder (oneCode scale re im)
open GaussianRationalReciprocal (power)
open GaussianIntegerFractionPowers (power_represents)
open GaussianIntegerFractionPowers (parityScalar parity_scalar_re parity_scalar_im parity_scalar_succ negative_power)
open LogarithmExponentialCoefficients (evenBit oddBit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def native (a : PTm n) : PTm n := scale a oneCode
def plusArgument (a b : PTm n) : PTm n := ofGaussian (native a) b
def minusArgument (a b : PTm n) : PTm n := ofGaussian (ComplexLogarithmRemainder.neg (native a)) b

@[simp] theorem subst_native {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (native a) = native (Syn.subst σ a) := by simp [native]
@[simp] theorem subst_plusArgument {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (plusArgument a b) = plusArgument (Syn.subst σ a) (Syn.subst σ b) := by simp [plusArgument]
@[simp] theorem subst_minusArgument {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (minusArgument a b) = minusArgument (Syn.subst σ a) (Syn.subst σ b) := by simp [minusArgument]

def realPowerLaw (a j : PTm n) : Fm PTm n :=
  equal (ComplexLogarithmRemainder.power (native a) j) (native (pw a j))

@[simp] theorem subst_realPowerLaw {m : ℕ} (σ : Fin n → PTm m) (a j : PTm n) :
    (realPowerLaw a j).subst σ = realPowerLaw (Syn.subst σ a) (Syn.subst σ j) := by simp [realPowerLaw]

theorem real_power_zero (a : PTm n) : Γ ⊢[PRAAx] realPowerLaw a zero := by
  have hp := values_of_code (ComplexLogarithmRemainder.power_zero (Γ := Γ) (native a))
  have hn := natEq (pw_zero (Γ := Γ) a)
  apply equal_of_values
  · rw [hp.1,re_one]
    simp only [native,re_scale,re_one,hn,Q.mk_one,map_one]
    ring
  · rw [hp.2,im_one]
    simp only [native,im_scale,im_one]
    ring

theorem real_power_step (a j : PTm n) (ih : Γ ⊢[PRAAx] realPowerLaw a j) :
    Γ ⊢[PRAAx] realPowerLaw a (succ j) := by
  have h := values_of_code (ComplexLogarithmRemainder.power_succ (Γ := Γ) (native a) j)
  have e := natEq (pw_succ (Γ := Γ) a j)
  have hr := equal_re ih
  have hi := equal_im ih
  apply equal_of_values
  · rw [h.1,re_mul,hr,hi]
    simp only [native,re_scale,im_scale,re_one,im_one]
    rw [e]
    ipra_simps
    ring
  · rw [h.2,im_mul,hr,hi]
    simp only [native,re_scale,im_scale,re_one,im_one]
    ring

theorem real_power (a j : PTm n) : Γ ⊢[PRAAx] realPowerLaw a j := by
  have formula : Γ ⊢[PRAAx] .all (realPowerLaw (Syn.shift a) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [subst_realPowerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact real_power_zero a
    · simp only [subst_realPowerLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact real_power_step _ _ Prf.hyp0
  simpa only [subst_realPowerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using formula.allE j

def evenLaw (K : PTm n) : Fm PTm n := evenBit (two*K) ≐ one ⋏ oddBit (two*K) ≐ zero
@[simp] theorem subst_evenLaw {m : ℕ} (σ : Fin n → PTm m) (K : PTm n) :
    (evenLaw K).subst σ = evenLaw (Syn.subst σ K) := by simp [evenLaw,evenBit,oddBit]

theorem parity_congr {x y : PTm n} (d : PTm n) (h : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx]
    eqb (rem x two) d ≐ eqb (rem y two) d := by
  have e := congrAp2 remF h (.eqRefl two)
  exact congrMonus (.eqRefl _) (congrAdd (congrMonus e (.eqRefl _)) (congrMonus (.eqRefl _) e))

theorem even_twice (K : PTm n) : Γ ⊢[PRAAx] evenLaw K := by
  have hall : Γ ⊢[PRAAx] .all (evenLaw (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [subst_evenLaw,Syn.subst_var,Syn.inst_zero]
      have e : Γ ⊢[PRAAx] two*zero ≐ zero := by ipra_ring
      exact .andI
        ((parity_congr zero e).eqTrans LogarithmExponentialCoefficients.evenBit_zero)
        ((parity_congr one e).eqTrans LogarithmExponentialCoefficients.oddBit_zero)
    · simp only [subst_evenLaw,Syn.subst_var,Syn.repl_zero]
      let C := evenLaw (var 0) :: Γ.map Fm.shift
      let j : PTm (n+1) := var 0
      have e : C ⊢[PRAAx] two*succ j ≐ succ (succ (two*j)) := by ipra_ring
      have p := AnalyticNumberTheory.Mobius.par_succ (Γ := C) (two*j)
      have p' := AnalyticNumberTheory.Mobius.par_succ (Γ := C) (succ (two*j))
      exact .andI
        ((parity_congr zero e).eqTrans
          (p'.andE₁.eqTrans (p.andE₂.eqTrans (Prf.andE₁ Prf.hyp0))))
        ((parity_congr one e).eqTrans
          (p'.andE₂.eqTrans (p.andE₁.eqTrans (Prf.andE₂ Prf.hyp0))))
  simpa only [subst_evenLaw,Syn.subst_var,Syn.inst_zero] using hall.allE K

theorem parity_even (K : PTm n) : Γ ⊢[PRAAx] equal (parityScalar (two*K)) oneCode := by
  have p := even_twice (Γ := Γ) K
  rw [evenLaw] at p
  apply equal_of_values
  · rw [parity_scalar_re,re_one,natEq p.andE₁,natEq p.andE₂]
    ipra_simps
    ring
  · rw [parity_scalar_im,im_one]

theorem parity_odd (K : PTm n) : Γ ⊢[PRAAx]
    equal (parityScalar (oddIndex K)) (ComplexLogarithmRemainder.neg oneCode) := by
  have h := parity_scalar_succ (Γ := Γ) (two*K)
  have e := parity_even (Γ := Γ) K
  unfold oddIndex
  apply equal_of_values
  · rw [equal_re h,re_neg,re_neg,equal_re e]
  · rw [equal_im h,im_neg,im_neg,equal_im e]

theorem parity_even_next (K : PTm n) : Γ ⊢[PRAAx] equal (parityScalar (succ (oddIndex K))) oneCode := by
  have h := parity_scalar_succ (Γ := Γ) (oddIndex K)
  have e := parity_odd (Γ := Γ) K
  apply equal_of_values
  · rw [equal_re h,re_neg,equal_re e,re_neg]
    ring
  · rw [equal_im h,im_neg,equal_im e,im_neg]
    ring

theorem negative_even_power (a j : PTm n) (h : Γ ⊢[PRAAx] equal (parityScalar j) oneCode) :
    Γ ⊢[PRAAx] equal
      (ComplexLogarithmRemainder.power (ComplexLogarithmRemainder.neg (native a)) j)
      (ComplexLogarithmRemainder.power (native a) j) := by
  have s := negative_power (Γ := Γ) (native a) j
  apply equal_of_values
  · rw [equal_re s,re_mul,equal_re h,equal_im h,re_one,im_one]
    ring
  · rw [equal_im s,im_mul,equal_re h,equal_im h,re_one,im_one]
    ring

theorem negative_odd_power (a K : PTm n) : Γ ⊢[PRAAx] equal
    (ComplexLogarithmRemainder.power (ComplexLogarithmRemainder.neg (native a)) (oddIndex K))
    (ComplexLogarithmRemainder.neg (native (AnalyticNumberTheory.RobinGamma.Pv K a))) := by
  let j := oddIndex K
  have s := negative_power (Γ := Γ) (native a) j
  have hp := parity_odd (Γ := Γ) K
  have u := real_power (Γ := Γ) a j
  apply equal_of_values
  · rw [equal_re s,re_mul,equal_re hp,equal_im hp,re_neg,im_neg,re_one,im_one,equal_re u]
    rw [re_neg]
    change _ = -ZT.toZ Γ (re (native (pw a j)))
    ring
  · rw [equal_im s,im_mul,equal_re hp,equal_im hp,re_neg,im_neg,re_one,im_one,equal_im u]
    rw [im_neg]
    change _ = -ZT.toZ Γ (im (native (pw a j)))
    ring

def logTerm (w k : PTm n) : PTm n := qmul (coefficient k) (power w (succ k))

theorem even_term_cancel (a b K : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qsub (logTerm (plusArgument a b) (oddIndex K)) (logTerm (minusArgument a b) (oddIndex K)) ≐ qzero := by
  let j := succ (oddIndex K)
  let u := ComplexLogarithmRemainder.power (native a) j
  have hd := ComplexLogarithmCauchy.power_positive b j hb
  have pa := power_represents (native a) b j hb
  have pb := power_represents (ComplexLogarithmRemainder.neg (native a)) b j hb
  have same : Γ ⊢[PRAAx] power (plusArgument a b) j ≐ power (minusArgument a b) j :=
    canonical_unique _ _ u (pw b j) (GaussianRationalReciprocal.power_canonical _ _)
      (GaussianRationalReciprocal.power_canonical _ _) hd pa
      (represents_congr (.eqRefl _) (negative_even_power a j (parity_even_next K)) (.eqRefl _) pb)
  exact (qsub_congr (.eqRefl _) (qmul_congr (.eqRefl _) same.eqSymm)).eqTrans
    (GaussianCoefficientNormOrder.qsub_self _)

theorem odd_term_value (a b K : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qsub (logTerm (plusArgument a b) (two*K)) (logTerm (minusArgument a b) (two*K)) ≐ term a b K := by
  let j := oddIndex K
  let A := AnalyticNumberTheory.RobinGamma.Pv K a
  let D := j*AnalyticNumberTheory.RobinGamma.Pv K b
  let v := native A
  let s := parityScalar (two*K)
  have he := parity_even (Γ := Γ) K
  have hpos := ComplexLogarithmCauchy.power_positive b j hb
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (zero_lt_succ _) hpos
  have c := coefficient_represents (Γ := Γ) (two*K)
  have plus := qmul_represents _ _ _ _ _ _ (zero_lt_succ _) hpos c (power_represents (native a) b j hb)
  have minu := qmul_represents _ _ _ _ _ _ (zero_lt_succ _) hpos c
    (power_represents (ComplexLogarithmRemainder.neg (native a)) b j hb)
  have hpa : Γ ⊢[PRAAx] equal
      (ComplexLogarithmRemainder.mul s (ComplexLogarithmRemainder.power (native a) j)) v := by
    have h := real_power (Γ := Γ) a j
    apply equal_of_values
    · rw [re_mul,equal_re he,equal_im he,re_one,im_one,equal_re h]
      change 1*ZT.toZ Γ (re v)-0*_ = ZT.toZ Γ (re v)
      ring
    · rw [im_mul,equal_re he,equal_im he,re_one,im_one,equal_im h]
      change 1*ZT.toZ Γ (im v)+0*_ = ZT.toZ Γ (im v)
      ring
  have hmb : Γ ⊢[PRAAx] equal
      (ComplexLogarithmRemainder.mul s
        (ComplexLogarithmRemainder.power (ComplexLogarithmRemainder.neg (native a)) j))
      (ComplexLogarithmRemainder.neg v) := by
    have h := negative_odd_power (Γ := Γ) a K
    apply equal_of_values
    · rw [re_mul,equal_re he,equal_im he,re_one,im_one,equal_re h]
      ring
    · rw [im_mul,equal_re he,equal_im he,re_one,im_one,equal_im h]
      ring
  have difference := qsub_represents _ _ _ _ D hd
    (represents_congr (.eqRefl _) hpa (.eqRefl _) plus) (represents_congr (.eqRefl _) hmb (.eqRefl _) minu)
  apply canonical_unique _ _ (native (two*A)) D (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hd) hd ?_ (ofGaussian_represents _ _ hd)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) difference
  apply equal_of_values <;> simp only [native,v,re_sub,im_sub,re_neg,im_neg,re_scale,im_scale,re_one,im_one] <;>
    (try ipra_simps) <;> ring

theorem log_two_steps (w K : PTm n) : Γ ⊢[PRAAx]
    value (two*succ K) w ≐ qadd (qadd (value (two*K) w) (logTerm w (two*K))) (logTerm w (oddIndex K)) := by
  have e : Γ ⊢[PRAAx] two*succ K ≐ succ (oddIndex K) := by unfold oddIndex; ipra_ring
  have once : Γ ⊢[PRAAx] value (oddIndex K) w ≐ qadd (value (two*K) w) (logTerm w (two*K)) := by
    simpa only [value,oddIndex,source_term_at,logTerm] using
      GaussianRationalFiniteSum.sum_succ (Γ := Γ) sourceTerm (two*K) w
  have twice := GaussianRationalFiniteSum.sum_succ (Γ := Γ) sourceTerm (oddIndex K) w
  rw [source_term_at] at twice
  exact (GaussianRationalFiniteSum.sum_index_congr sourceTerm e (.eqRefl _)).eqTrans
    (twice.eqTrans (qadd_congr once (.eqRefl _)))

def parityLaw (a b K : PTm n) : Fm PTm n :=
  qsub (value (two*K) (plusArgument a b)) (value (two*K) (minusArgument a b)) ≐ oddSum a b K
@[simp] theorem subst_parityLaw {m : ℕ} (σ : Fin n → PTm m) (a b K : PTm n) :
    (parityLaw a b K).subst σ = parityLaw (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ K) := by simp [parityLaw]

theorem parity_zero (a b : PTm n) : Γ ⊢[PRAAx] parityLaw a b zero := by
  have e : Γ ⊢[PRAAx] two*zero ≐ zero := by ipra_ring
  have h (w : PTm n) : Γ ⊢[PRAAx] value (two*zero) w ≐ qzero :=
    (GaussianRationalFiniteSum.sum_index_congr sourceTerm e (.eqRefl _)).eqTrans
      (GaussianRationalFiniteSum.sum_zero sourceTerm w)
  exact (qsub_congr (h _) (h _)).eqTrans ((GaussianCoefficientNormOrder.qsub_self _).eqTrans
    (GaussianRationalFiniteSum.sum_zero GaussianRobinOddLogarithm.body (pairT a b)).eqSymm)

theorem parity_step (a b K : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ih : Γ ⊢[PRAAx] parityLaw a b K) :
    Γ ⊢[PRAAx] parityLaw a b (succ K) := by
  let w := plusArgument a b
  let v := minusArgument a b
  let A := value (two*K) w
  let B := value (two*K) v
  let c := logTerm w (two*K)
  let d := logTerm v (two*K)
  let e := logTerm w (oddIndex K)
  let f := logTerm v (oddIndex K)
  have h := qsub_congr (Γ := Γ) (log_two_steps w K) (log_two_steps v K)
  have eA := GaussianNameArithmetic.sum_difference (Γ := Γ) (qadd A c) (qadd B d) e f
  have eB := GaussianNameArithmetic.sum_difference (Γ := Γ) A B c d
  have eC := qadd_congr (qadd_congr ih (odd_term_value a b K hb)) (even_term_cancel a b K hb)
  have base := GaussianReciprocalHorner.qadd_zero_right (Γ := Γ) _ (GaussianRationalHorner.qadd_canonical (oddSum a b K) (term a b K))
  exact h.eqTrans (eA.eqTrans ((qadd_congr eB (.eqRefl _)).eqTrans
    (eC.eqTrans (base.eqTrans (GaussianRobinOddLogarithm.returned_sum_step a b K).eqSymm))))

theorem parity_identity (a b K : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] parityLaw a b K := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hb.shift
  have all : Γ ⊢[PRAAx] .all (parityLaw (Syn.shift a) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_parityLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact parity_zero a b
    · simp only [subst_parityLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact parity_step _ _ _ hs.wk Prf.hyp0
  simpa only [subst_parityLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K

theorem original_Robin_logarithm_parity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ parityLaw (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (parity_identity _ _ _ Prf.hyp0))

def robinComparison (a b K : PTm n) : Fm PTm n :=
  qsub (value (two*K) (plusArgument a b)) (value (two*K) (minusArgument a b)) ≐
    RationalGaussianEmbedding.embed
      (RationalCubeMidpoint.fraction (AnalyticNumberTheory.RobinLogName.Nz K a b)
        (AnalyticNumberTheory.RobinLogName.Dz K a b))

theorem original_Robin_logarithm_value (a b K : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] robinComparison a b K :=
  (parity_identity a b K hb).eqTrans (GaussianRobinOddLogarithm.embedded_value a b K hb).eqSymm

theorem original_Robin_logarithm_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ robinComparison (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (original_Robin_logarithm_value _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRobinLogarithmParity
