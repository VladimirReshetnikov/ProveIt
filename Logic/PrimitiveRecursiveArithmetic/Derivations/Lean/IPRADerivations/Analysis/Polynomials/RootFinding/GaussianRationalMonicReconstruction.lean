import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalMonicReduction
import IPRADerivations.Analysis.Polynomials.GaussianRationalPolynomialProduct
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Coefficient reconstruction for the actual monic reduction

The theorem compares actual bounded entries of the original padded input,
the runtime coefficient-convolution product of P and the returned quotient,
and the padded returned remainder. It uses no evaluator identity as an
input and makes no claim that arbitrary outer list codes are equal. All
original degrees, data, counters and coefficient indices are numerical.
The common stored width is D+M+2; the original input is normalized only at
coefficient observations. This exact Q(i) reconstruction does not yet
construct an extension field, multiplication matrix, determinant or norm.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalMonicReconstruction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qadd_congr qmul_congr qzero_canonical qmul_zero_left qmul_zero_right qzero_add canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct
  (padded padded_inside padded_outside padded_congr padded_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
  (appendZero append_length append_lookup leftPad pad_length pad_lookup pad_leading pad_tail
    added added_lookup added_length)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProduct
  (contribution coefficient contribution_inside contribution_outside coefficient_zero coefficient_succ)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction
  (singleton constant quotient remainder quotientNext remainderNext reducedQuotient reducedRemainder)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_canonical recode_eq)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticCoefficientValues
  (qadd_recode_left qadd_recode_right qmul_recode_left qmul_recode_right)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem le_or_lt (a b : PTm n) : Γ ⊢[PRAAx] le a b ⋎ lt b a :=
  .orE (lt_or_le b a) (.orI₂ Prf.hyp0) (.orI₁ Prf.hyp0)
alias monus_le_left := Common.monus_le_self

theorem zero_add_zero : Γ ⊢[PRAAx] qadd qzero qzero ≐ qzero := qzero_add qzero qzero_canonical

theorem padded_added (A B L j : PTm n) : Γ ⊢[PRAAx]
    padded (added A B L) L j ≐ qadd (padded A L j) (padded B L j) := by
  refine .orE (lt_or_le j L) ?_ ?_
  · exact (padded_inside _ _ _ Prf.hyp0).eqTrans
      ((added_lookup A B L j Prf.hyp0).eqTrans
        (qadd_congr (padded_inside A L j Prf.hyp0).eqSymm (padded_inside B L j Prf.hyp0).eqSymm))
  · exact (padded_outside _ _ _ Prf.hyp0).eqTrans
      (zero_add_zero.eqSymm.eqTrans
        (qadd_congr (padded_outside A L j Prf.hyp0).eqSymm (padded_outside B L j Prf.hyp0).eqSymm))

theorem padded_append (Q M j : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    padded (appendZero Q) (succ (succ M)) j ≐ padded Q (succ M) j := by
  refine .orE (lt_or_le j (succ (succ M))) ?_ ?_
  · have range : _ ⊢[PRAAx] le j (length Q) :=
      le_congr (.eqRefl _) hQ.wk.eqSymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
    exact (padded_inside _ _ _ Prf.hyp0).eqTrans
      ((append_lookup Q j range).eqTrans (padded_congr (.eqRefl _) hQ.wk (.eqRefl _)))
  · exact (padded_outside _ _ _ Prf.hyp0).eqTrans
      (padded_outside Q (succ M) j (le_trans (le_succ_self _) Prf.hyp0)).eqSymm

theorem contribution_added (P A B M k i : PTm n) : Γ ⊢[PRAAx]
    contribution P (added A B (succ M)) M k i ≐
      qadd (contribution P A M k i) (contribution P B M k i) := by
  refine .orE (le_or_lt i k) ?_ ?_
  · exact (contribution_inside _ _ _ _ _ Prf.hyp0).eqTrans
      ((qmul_congr (.eqRefl _) (padded_added _ _ _ _)).eqTrans
        ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
          (qadd_congr (contribution_inside _ _ _ _ _ Prf.hyp0).eqSymm
            (contribution_inside _ _ _ _ _ Prf.hyp0).eqSymm)))
  · exact (contribution_outside _ _ _ _ _ Prf.hyp0).eqTrans
      (zero_add_zero.eqSymm.eqTrans
        (qadd_congr (contribution_outside _ _ _ _ _ Prf.hyp0).eqSymm
          (contribution_outside _ _ _ _ _ Prf.hyp0).eqSymm))

def addLaw (P A B M k t : PTm n) : Fm PTm n :=
  coefficient P (added A B (succ M)) M t k ≐ qadd (coefficient P A M t k) (coefficient P B M t k)
@[simp] theorem subst_addLaw {l : ℕ} (σ : Fin n → PTm l) (P A B M k t : PTm n) :
    (addLaw P A B M k t).subst σ = addLaw (Syn.subst σ P) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ M) (Syn.subst σ k) (Syn.subst σ t) := by simp [addLaw]

theorem coefficient_added (P A B M t k : PTm n) : Γ ⊢[PRAAx] addLaw P A B M k t := by
  have all : Γ ⊢[PRAAx] .all (addLaw (Syn.shift P) (Syn.shift A) (Syn.shift B) (Syn.shift M) (Syn.shift k) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_addLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (coefficient_zero _ _ _ _).eqTrans
        ((qadd_congr (coefficient_zero _ _ _ _) (coefficient_zero _ _ _ _)).eqTrans zero_add_zero).eqSymm
    · simp only [subst_addLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (coefficient_succ _ _ _ _ _).eqTrans
        ((qadd_congr Prf.hyp0 (contribution_added _ _ _ _ _ _)).eqTrans
          ((GaussianRationalFiniteSum.add_shuffle _ _ _ _).eqTrans
            (qadd_congr (coefficient_succ _ _ _ _ _).eqSymm (coefficient_succ _ _ _ _ _).eqSymm)))
  simpa only [subst_addLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t

def paddedEqual (Q Q' M M' k : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift k) ⟶ padded (Syn.shift Q) (succ (Syn.shift M)) (var 0) ≐
    padded (Syn.shift Q') (succ (Syn.shift M')) (var 0))
@[simp] theorem subst_paddedEqual {l : ℕ} (σ : Fin n → PTm l) (Q Q' M M' k : PTm n) :
    (paddedEqual Q Q' M M' k).subst σ = paddedEqual (Syn.subst σ Q) (Syn.subst σ Q')
      (Syn.subst σ M) (Syn.subst σ M') (Syn.subst σ k) := by simp [paddedEqual,Syn.subst_shift,Syn.shift_subst]
theorem padded_equal_at (Q Q' M M' k j : PTm n) (h : Γ ⊢[PRAAx] paddedEqual Q Q' M M' k)
    (hj : Γ ⊢[PRAAx] le j k) : Γ ⊢[PRAAx] padded Q (succ M) j ≐ padded Q' (succ M') j := by
  have gate : Γ ⊢[PRAAx] le j k ⟶ padded Q (succ M) j ≐ padded Q' (succ M') j := by
    simpa only [paddedEqual,Fm.subst_imp,Fm.subst_eq,subst_le,GaussianRationalLinearProduct.subst_padded,
      ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j
  exact .impE gate hj

theorem coefficient_padded_ext (P Q Q' M M' t k : PTm n)
    (h : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift k) ⟶
      padded (Syn.shift Q) (succ (Syn.shift M)) (var 0) ≐ padded (Syn.shift Q') (succ (Syn.shift M')) (var 0))) : Γ ⊢[PRAAx]
    coefficient P Q M t k ≐ coefficient P Q' M' t k := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift t) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] paddedEqual (Syn.shift Q) (Syn.shift Q') (Syn.shift M) (Syn.shift M') (Syn.shift k) := by
    simpa only [Fm.shift,subst_paddedEqual,Syn.shift] using (show Γ ⊢[PRAAx] paddedEqual Q Q' M M' k from h).shift.wk
  have pad := padded_equal_at (Γ := Δ) _ _ _ _ _ (monus (Syn.shift k) (var 0)) hs (monus_le_left _ _)
  have term : Δ ⊢[PRAAx]
      contribution (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift k) (var 0) ≐
        contribution (Syn.shift P) (Syn.shift Q') (Syn.shift M') (Syn.shift k) (var 0) := by
    refine .orE (le_or_lt (var 0) (Syn.shift k)) ?_ ?_
    · exact (contribution_inside _ _ _ _ _ Prf.hyp0).eqTrans
        ((qmul_congr (.eqRefl _) pad.wk).eqTrans (contribution_inside _ _ _ _ _ Prf.hyp0).eqSymm)
    · exact (contribution_outside _ _ _ _ _ Prf.hyp0).eqTrans (contribution_outside _ _ _ _ _ Prf.hyp0).eqSymm
  simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_data] using
    (GaussianRationalPolynomialProduct.contribution_body_at _ _ _ _ _).eqTrans
      (term.eqTrans (GaussianRationalPolynomialProduct.contribution_body_at _ _ _ _ _).eqSymm)

def spike (a q i : PTm n) : PTm n := RationalArithmetic.select (eqb i a) qzero q
def active (a q t : PTm n) : PTm n := RationalArithmetic.select (Signum.sg (monus t a)) qzero q
def spikeData (a q : PTm n) : PTm n := pairT a q
def spikeBody : PTm 2 := spike (fstT (var 1)) (sndT (var 1)) (var 0)
def spikeSum (a q t : PTm n) : PTm n := GaussianRationalFiniteSum.sum spikeBody t (spikeData a q)
@[simp] theorem subst_spike {l : ℕ} (σ : Fin n → PTm l) (a q i : PTm n) :
    Syn.subst σ (spike a q i) = spike (Syn.subst σ a) (Syn.subst σ q) (Syn.subst σ i) := by simp [spike]
@[simp] theorem subst_active {l : ℕ} (σ : Fin n → PTm l) (a q t : PTm n) :
    Syn.subst σ (active a q t) = active (Syn.subst σ a) (Syn.subst σ q) (Syn.subst σ t) := by simp [active,Signum.sg]
@[simp] theorem subst_spikeData {l : ℕ} (σ : Fin n → PTm l) (a q : PTm n) :
    Syn.subst σ (spikeData a q) = spikeData (Syn.subst σ a) (Syn.subst σ q) := by simp [spikeData]
@[simp] theorem subst_spikeSum {l : ℕ} (σ : Fin n → PTm l) (a q t : PTm n) :
    Syn.subst σ (spikeSum a q t) = spikeSum (Syn.subst σ a) (Syn.subst σ q) (Syn.subst σ t) := by simp [spikeSum]

theorem select_congr {b b' u u' v v' : PTm n} (hb : Γ ⊢[PRAAx] b ≐ b')
    (hu : Γ ⊢[PRAAx] u ≐ u') (hv : Γ ⊢[PRAAx] v ≐ v') : Γ ⊢[PRAAx]
    RationalArithmetic.select b u v ≐ RationalArithmetic.select b' u' v' :=
  congrAdd (congrMul hb hv) (congrMul (congrMonus (.eqRefl _) hb) hu)
theorem spike_congr {a a' q q' i i' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a')
    (hq : Γ ⊢[PRAAx] q ≐ q') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    spike a q i ≐ spike a' q' i' := select_congr (AnalyticNumberTheory.Euler.congrEqb hi ha) (.eqRefl _) hq

alias different_of_lt := Common.ne_of_lt
theorem different_of_gt {a b : PTm n} (h : Γ ⊢[PRAAx] lt b a) : Γ ⊢[PRAAx] neg (a ≐ b) :=
  .impI (lt_irrefl _ _ (lt_congr (.eqRefl _) Prf.hyp0 h.wk))
theorem spike_hit (a q i : PTm n) (h : Γ ⊢[PRAAx] i ≐ a) : Γ ⊢[PRAAx] spike a q i ≐ q :=
  RationalArithmetic.select_one _ _ _ (eqb_of_eq h)
theorem spike_miss (a q i : PTm n) (h : Γ ⊢[PRAAx] neg (i ≐ a)) : Γ ⊢[PRAAx] spike a q i ≐ qzero :=
  RationalArithmetic.select_zero _ _ _ (eqb_of_ne h)
theorem active_on (a q t : PTm n) (h : Γ ⊢[PRAAx] lt a t) : Γ ⊢[PRAAx] active a q t ≐ q :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt h)
theorem active_off (a q t : PTm n) (h : Γ ⊢[PRAAx] le t a) : Γ ⊢[PRAAx] active a q t ≐ qzero :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le h)

theorem spike_body_at (a q i : PTm n) : Γ ⊢[PRAAx] inst2 spikeBody i (spikeData a q) ≐ spike a q i := by
  simp only [spikeBody,inst2,subst_spike,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact spike_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)
theorem spike_sum_succ (a q t : PTm n) : Γ ⊢[PRAAx]
    spikeSum a q (succ t) ≐ qadd (spikeSum a q t) (spike a q t) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (spike_body_at a q t))

theorem spike_sum_step (a q t : PTm n) (hq : Γ ⊢[PRAAx] canonical q)
    (h : Γ ⊢[PRAAx] spikeSum a q t ≐ active a q t) : Γ ⊢[PRAAx]
    spikeSum a q (succ t) ≐ active a q (succ t) := by
  refine .orE (lt_or_le a t) ?_ ?_
  · exact (spike_sum_succ _ _ _).eqTrans
      ((qadd_congr (h.wk.eqTrans (active_on _ _ _ Prf.hyp0)) (spike_miss _ _ _ (different_of_gt Prf.hyp0))).eqTrans
        ((GaussianRationalLinearProduct.qadd_zero_right q hq.wk).eqTrans
          (active_on _ _ _ (lt_of_lt_of_le Prf.hyp0 (le_succ_self _))).eqSymm))
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · exact (spike_sum_succ _ _ _).eqTrans
        ((qadd_congr (h.wk.wk.eqTrans (active_off _ _ _ (le_of_lt Prf.hyp0)))
          (spike_miss _ _ _ (different_of_lt Prf.hyp0))).eqTrans
            (zero_add_zero.eqTrans (active_off _ _ _ Prf.hyp0).eqSymm))
    · exact (spike_sum_succ _ _ _).eqTrans
        ((qadd_congr (h.wk.wk.eqTrans (active_off _ _ _ (le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl a)))) (spike_hit _ _ _ Prf.hyp0)).eqTrans
          ((qzero_add q hq.wk.wk).eqTrans
            (active_on _ _ _ (lt_congr Prf.hyp0 (.eqRefl _) (le_refl (succ t)))).eqSymm))

theorem spike_sum (a q t : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx]
    spikeSum a q t ≐ active a q t := by
  have qs : Γ.map Fm.shift ⊢[PRAAx] canonical (Syn.shift q) := by
    simpa only [Fm.shift,GaussianRationalHorner.subst_canonical,Syn.shift] using hq.shift
  have all : Γ ⊢[PRAAx] .all (spikeSum (Syn.shift a) (Syn.shift q) (var 0) ≐ active (Syn.shift a) (Syn.shift q) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_spikeSum,subst_active,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans (active_off a q zero (zero_le a)).eqSymm
    · simp only [Fm.subst_eq,subst_spikeSum,subst_active,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact spike_sum_step _ _ _ qs.wk Prf.hyp0
  simpa only [Fm.subst_eq,subst_spikeSum,subst_active,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t

theorem leftPad_congr {C C' a a' : PTm n} (hC : Γ ⊢[PRAAx] C ≐ C') (ha : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx]
    leftPad C a ≐ leftPad C' a' := by
  ipra_congr (leftPad (var 0) (var 1) : PTm 2) with [hC, ha]
theorem constant_code (c a : PTm n) : Γ ⊢[PRAAx] constant c (succ a) ≐ leftPad (singleton c) a :=
  leftPad_congr (.eqRefl _) (pred_succ a)
theorem constant_padded (c a j : PTm n) : Γ ⊢[PRAAx]
    padded (constant c (succ a)) (succ a) j ≐ spike a c j := by
  refine .orE (lt_or_le j (succ a)) ?_ ?_
  · have value : lt j (succ a) :: Γ ⊢[PRAAx]
        padded (constant c (succ a)) (succ a) j ≐ entry (leftPad (singleton c) a) j :=
      (padded_inside (constant c (succ a)) (succ a) j Prf.hyp0).eqTrans
      (entry_congr (constant_code c a) (.eqRefl _))
    have ja : lt j (succ a) :: Γ ⊢[PRAAx] le j a := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    refine .orE (lt_or_eq_of_le ja) ?_ ?_
    · exact value.wk.eqTrans ((pad_leading _ _ _ Prf.hyp0).eqTrans
        (spike_miss _ _ _ (different_of_lt Prf.hyp0)).eqSymm)
    · have atOffset : (j ≐ a) :: lt j (succ a) :: Γ ⊢[PRAAx] entry (leftPad (singleton c) a) j ≐ c :=
        (entry_congr (.eqRefl _) Prf.hyp0).eqTrans
          ((entry_congr (.eqRefl _) (add_zero a).eqSymm).eqTrans
            ((pad_tail _ _ zero (le_congr (.eqRefl _) (GaussianRationalMonicReduction.singleton_length c).eqSymm (le_refl one))).eqTrans
              (GaussianRationalMonicReduction.singleton_lookup c)))
      exact value.wk.eqTrans (atOffset.eqTrans (spike_hit _ _ _ Prf.hyp0).eqSymm)
  · exact (padded_outside _ _ _ Prf.hyp0).eqTrans (spike_miss _ _ _ (different_of_gt Prf.hyp0)).eqSymm

theorem complement (k a : PTm n) (ha : Γ ⊢[PRAAx] le a k) : Γ ⊢[PRAAx] monus k (monus k a) ≐ a :=
  (congrMonus (eq_add_of_le ha) (.eqRefl _)).eqTrans (add_monus _ _)

theorem contribution_constant (P c a k i : PTm n) (ha : Γ ⊢[PRAAx] le a k) : Γ ⊢[PRAAx]
    contribution P (constant c (succ a)) a k i ≐ spike (monus k a) (qmul (entry P (monus k a)) c) i := by
  refine .orE (le_or_lt i k) ?_ ?_
  · have inside : le i k :: Γ ⊢[PRAAx] le i k := Prf.hyp0
    have actual : le i k :: Γ ⊢[PRAAx] contribution P (constant c (succ a)) a k i ≐
        qmul (entry P i) (spike a c (monus k i)) :=
      (contribution_inside P (constant c (succ a)) a k i Prf.hyp0).eqTrans
      (qmul_congr (.eqRefl _) (constant_padded c a (monus k i)))
    refine .orE (eq_or_ne i (monus k a)) ?_ ?_
    · have reverse : (i ≐ monus k a) :: le i k :: Γ ⊢[PRAAx] monus k i ≐ a :=
        (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (complement k a ha.wk.wk)
      exact actual.wk.eqTrans
        ((qmul_congr (.eqRefl _) (spike_hit _ _ _ reverse)).eqTrans
          ((qmul_congr (entry_congr (.eqRefl _) Prf.hyp0) (.eqRefl _)).eqTrans (spike_hit _ _ _ Prf.hyp0).eqSymm))
    · have miss : neg (i ≐ monus k a) :: le i k :: Γ ⊢[PRAAx] neg (monus k i ≐ a) := by
        refine .impI ?_
        have idx : (monus k i ≐ a) :: neg (i ≐ monus k a) :: le i k :: Γ ⊢[PRAAx] monus k a ≐ i :=
          (congrMonus (eq_add_of_le inside.wk.wk) (.eqRefl _)).eqTrans
            ((congrMonus (congrAdd (.eqRefl _) Prf.hyp0) (.eqRefl _)).eqTrans (add_monus i a))
        exact .impE Prf.hyp1 idx.eqSymm
      exact actual.wk.eqTrans
        ((qmul_congr (.eqRefl _) (spike_miss _ _ _ miss)).eqTrans
          ((qmul_zero_right _).eqTrans (spike_miss _ _ _ Prf.hyp0).eqSymm))
  · exact (contribution_outside _ _ _ _ _ Prf.hyp0).eqTrans
      (spike_miss _ _ _ (different_of_gt (lt_of_le_of_lt (monus_le_left k a) Prf.hyp0))).eqSymm

def offsetCoefficient (P c t a k : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg (monus (succ k) a)) qzero (qmul c (padded P t (monus k a)))
@[simp] theorem subst_offsetCoefficient {l : ℕ} (σ : Fin n → PTm l) (P c t a k : PTm n) :
    Syn.subst σ (offsetCoefficient P c t a k) = offsetCoefficient (Syn.subst σ P) (Syn.subst σ c)
      (Syn.subst σ t) (Syn.subst σ a) (Syn.subst σ k) := by simp [offsetCoefficient,Signum.sg]
theorem offset_on (P c t a k : PTm n) (ha : Γ ⊢[PRAAx] le a k) : Γ ⊢[PRAAx]
    offsetCoefficient P c t a k ≐ qmul c (padded P t (monus k a)) :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt ((succ_monus_succ _ _).eqTrans ha))
theorem offset_off (P c t a k : PTm n) (ha : Γ ⊢[PRAAx] lt k a) : Γ ⊢[PRAAx]
    offsetCoefficient P c t a k ≐ qzero :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le ha)

theorem coefficient_constant (P c a t k : PTm n) : Γ ⊢[PRAAx]
    coefficient P (constant c (succ a)) a t k ≐ offsetCoefficient P c t a k := by
  refine .orE (le_or_lt a k) ?_ ?_
  · have as : (le a k :: Γ).map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift k) := by
      simpa only [Fm.shift,subst_le,Syn.shift] using (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := le a k)).shift
    have sum : (le a k :: Γ) ⊢[PRAAx] coefficient P (constant c (succ a)) a t k ≐
        spikeSum (monus k a) (qmul (entry P (monus k a)) c) t := by
      apply GaussianRationalFiniteSum.sum_congr_bounded
      refine .allI (.impI ?_)
      let Δ := lt (var 0) (Syn.shift t) :: (le a k :: Γ).map Fm.shift
      have h := contribution_constant (Γ := Δ) (Syn.shift P) (Syn.shift c) (Syn.shift a) (Syn.shift k) (var 0) as.wk
      simpa only [Δ,Fm.shift,subst_le,Syn.shift,GaussianRationalPolynomialProduct.subst_data,
        GaussianRationalMonicReduction.subst_constant,ConciseIPRA.PTm.subst_succ,subst_spikeData,
        GaussianRationalHorner.subst_qmul,Foundations.MasterCertificate.subst_entry,PTm.subst_monus] using
        (GaussianRationalPolynomialProduct.contribution_body_at _ _ _ _ _).eqTrans
          (h.eqTrans (spike_body_at _ _ _).eqSymm)
    have hit := sum.eqTrans (spike_sum _ _ _ (GaussianRationalHorner.qmul_canonical _ _))
    refine hit.eqTrans ?_
    refine .orE (lt_or_le (monus k a) t) ?_ ?_
    · exact (active_on _ _ _ Prf.hyp0).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
          ((qmul_congr (.eqRefl _) (padded_inside _ _ _ Prf.hyp0).eqSymm).eqTrans (offset_on _ _ _ _ _ Prf.hyp1).eqSymm))
    · exact (active_off _ _ _ Prf.hyp0).eqTrans
        ((qmul_zero_right c).eqSymm.eqTrans
          ((qmul_congr (.eqRefl _) (padded_outside _ _ _ Prf.hyp0).eqSymm).eqTrans (offset_on _ _ _ _ _ Prf.hyp1).eqSymm))
  · have ks : (lt k a :: Γ).map Fm.shift ⊢[PRAAx] lt (Syn.shift k) (Syn.shift a) := by
      simpa only [Fm.shift,subst_lt,Syn.shift] using (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := lt k a)).shift
    have eqs : (lt k a :: Γ) ⊢[PRAAx]
        GaussianRationalFiniteSum.termsEqual GaussianRationalPolynomialProduct.contributionBody (qzero : PTm 2)
          t (GaussianRationalPolynomialProduct.data P (constant c (succ a)) a k) zero := by
      refine .allI (.impI ?_)
      let Δ := lt (var 0) (Syn.shift t) :: (lt k a :: Γ).map Fm.shift
      have value : Δ ⊢[PRAAx] contribution (Syn.shift P) (constant (Syn.shift c) (succ (Syn.shift a)))
          (Syn.shift a) (Syn.shift k) (var 0) ≐ qzero := by
        refine .orE (le_or_lt (var 0) (Syn.shift k)) ?_ ?_
        · exact (contribution_inside _ _ _ _ _ Prf.hyp0).eqTrans
            ((qmul_congr (.eqRefl _) ((constant_padded _ _ _).eqTrans
              (spike_miss _ _ _ (different_of_lt (lt_of_le_of_lt (monus_le_left _ _) ks.wk.wk))))).eqTrans (qmul_zero_right _))
        · exact contribution_outside _ _ _ _ _ Prf.hyp0
      simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_data,GaussianRationalMonicReduction.subst_constant,
        ConciseIPRA.PTm.subst_succ,inst2,GaussianRationalHorner.subst_qzero] using
          (GaussianRationalPolynomialProduct.contribution_body_at _ _ _ _ _).eqTrans value
    exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ eqs).eqTrans
      ((GaussianRationalPolynomialProduct.constant_zero_sum _ _).eqTrans (offset_off _ _ _ _ _ Prf.hyp0).eqSymm)

theorem coefficient_append (P Q M t k : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    coefficient P (appendZero Q) (succ M) t k ≐ coefficient P Q M t k := by
  apply coefficient_padded_ext
  refine .allI (.impI ?_)
  have qs : (le (var 0) (Syn.shift k)) :: Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift Q) ≐ succ (Syn.shift M) := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hQ.shift.wk
  simpa only [Syn.shift,GaussianRationalPolynomialBuffers.subst_appendZero,ConciseIPRA.PTm.subst_succ] using
    padded_append (Syn.shift Q) (Syn.shift M) (var 0) qs

theorem coefficient_quotient_next (P Q R r t k : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ r) : Γ ⊢[PRAAx]
    coefficient P (quotientNext Q R r) (succ r) t k ≐
      qadd (coefficient P Q r t k) (offsetCoefficient P (GaussianRationalMonicCompanion.lead R) t (succ r) k) :=
  (coefficient_added _ _ _ _ _ _).eqTrans
    (qadd_congr (coefficient_append P Q r t k hQ) (coefficient_constant _ _ _ _ _))

def shifted (C L a k : PTm n) : PTm n :=
  RationalArithmetic.select (Signum.sg (monus (succ k) a)) qzero (padded C L (monus k a))
@[simp] theorem subst_shifted {l : ℕ} (σ : Fin n → PTm l) (C L a k : PTm n) :
    Syn.subst σ (shifted C L a k) = shifted (Syn.subst σ C) (Syn.subst σ L) (Syn.subst σ a) (Syn.subst σ k) := by simp [shifted,Signum.sg]
theorem shifted_congr {C C' L L' a a' k k' : PTm n} (hC : Γ ⊢[PRAAx] C ≐ C')
    (hL : Γ ⊢[PRAAx] L ≐ L') (ha : Γ ⊢[PRAAx] a ≐ a') (hk : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx]
    shifted C L a k ≐ shifted C' L' a' k' :=
  select_congr (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus (congrSucc hk) ha)))
    (.eqRefl _) (padded_congr hC hL (congrMonus hk ha))
theorem shifted_on (C L a k : PTm n) (ha : Γ ⊢[PRAAx] le a k) : Γ ⊢[PRAAx]
    shifted C L a k ≐ padded C L (monus k a) :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt ((succ_monus_succ _ _).eqTrans ha))
theorem shifted_off (C L a k : PTm n) (ha : Γ ⊢[PRAAx] lt k a) : Γ ⊢[PRAAx]
    shifted C L a k ≐ qzero := RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le ha)
theorem shifted_at_add (C L a j : PTm n) : Γ ⊢[PRAAx] shifted C L a (a+j) ≐ padded C L j :=
  (shifted_on _ _ _ _ (le_add_right _ _)).eqTrans (padded_congr (.eqRefl _) (.eqRefl _) (add_monus' j a))

theorem shifted_compose (C L a b j : PTm n) : Γ ⊢[PRAAx]
    shifted C L (a+b) (a+j) ≐ shifted C L b j := by
  refine .orE (lt_or_le j b) ?_ ?_
  · have ltSum : lt j b :: Γ ⊢[PRAAx] lt (a+j) (a+b) :=
      le_congr (by ipra_ring : _ ⊢[PRAAx] a+succ j ≐ succ (a+j)) (.eqRefl _)
        (add_le_add₂ (le_refl a) Prf.hyp0)
    exact (shifted_off _ _ _ _ ltSum).eqTrans (shifted_off _ _ _ _ Prf.hyp0).eqSymm
  · have index : le b j :: Γ ⊢[PRAAx] a+j ≐ (a+b)+monus j b :=
      (congrAdd (.eqRefl _) (eq_add_of_le Prf.hyp0)).eqTrans (by ipra_ring)
    exact (shifted_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) index).eqTrans
      ((shifted_at_add _ _ _ _).eqTrans
        ((shifted_at_add C L b (monus j b)).eqSymm.eqTrans
          (shifted_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (eq_add_of_le Prf.hyp0).eqSymm)))

theorem offset_as_multiply (P c t a k : PTm n) : Γ ⊢[PRAAx]
    offsetCoefficient P c t a k ≐ qmul c (shifted P t a k) := by
  refine .orE (le_or_lt a k) ?_ ?_
  · exact (offset_on _ _ _ _ _ Prf.hyp0).eqTrans
      (qmul_congr (.eqRefl _) (shifted_on _ _ _ _ Prf.hyp0).eqSymm)
  · exact (offset_off _ _ _ _ _ Prf.hyp0).eqTrans
      ((qmul_zero_right c).eqSymm.eqTrans (qmul_congr (.eqRefl _) (shifted_off _ _ _ _ Prf.hyp0).eqSymm))

theorem shifted_added (C E L a k : PTm n) : Γ ⊢[PRAAx]
    shifted (added C E L) L a k ≐ qadd (shifted C L a k) (shifted E L a k) := by
  refine .orE (le_or_lt a k) ?_ ?_
  · exact (shifted_on _ _ _ _ Prf.hyp0).eqTrans
      ((padded_added _ _ _ _).eqTrans
        (qadd_congr (shifted_on _ _ _ _ Prf.hyp0).eqSymm (shifted_on _ _ _ _ Prf.hyp0).eqSymm))
  · exact (shifted_off _ _ _ _ Prf.hyp0).eqTrans
      (zero_add_zero.eqSymm.eqTrans
        (qadd_congr (shifted_off _ _ _ _ Prf.hyp0).eqSymm (shifted_off _ _ _ _ Prf.hyp0).eqSymm))

theorem padded_zeros (L j : PTm n) : Γ ⊢[PRAAx]
    padded (GaussianRationalPolynomialBuffers.zeros L) L j ≐ qzero := by
  refine .orE (lt_or_le j L) ?_ ?_
  · exact (padded_inside _ _ _ Prf.hyp0).eqTrans (GaussianRationalPolynomialBuffers.zeros_lookup _ _ Prf.hyp0)
  · exact padded_outside _ _ _ Prf.hyp0
theorem shifted_zeros (L a k : PTm n) : Γ ⊢[PRAAx]
    shifted (GaussianRationalPolynomialBuffers.zeros L) L a k ≐ qzero := by
  refine .orE (le_or_lt a k) ?_ ?_
  · exact (shifted_on _ _ _ _ Prf.hyp0).eqTrans (padded_zeros _ _)
  · exact shifted_off _ _ _ _ Prf.hyp0
theorem shifted_empty (C a k : PTm n) : Γ ⊢[PRAAx] shifted C zero a k ≐ qzero := by
  refine .orE (le_or_lt a k) ?_ ?_
  · exact (shifted_on _ _ _ _ Prf.hyp0).eqTrans (padded_outside _ _ _ (zero_le _))
  · exact shifted_off _ _ _ _ Prf.hyp0

theorem subtract_bound (a L k : PTm n) (ha : Γ ⊢[PRAAx] le a k) (hk : Γ ⊢[PRAAx] lt k (a+L)) : Γ ⊢[PRAAx]
    lt (monus k a) L := by
  apply le_of_eq_add (d := monus (a+L) (succ k))
  ipra_lc natEq (eq_add_of_le hk)+natEq (eq_add_of_le ha)

theorem shifted_pad_entry (C L a k : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ L)
    (hk : Γ ⊢[PRAAx] lt k (a+L)) : Γ ⊢[PRAAx]
    shifted C L a k ≐ entry (leftPad C a) k := by
  refine .orE (lt_or_le k a) ?_ ?_
  · exact (shifted_off _ _ _ _ Prf.hyp0).eqTrans (pad_leading _ _ _ Prf.hyp0).eqSymm
  · have sub := subtract_bound a L k Prf.hyp0 hk.wk
    have decode : _ ⊢[PRAAx] entry (leftPad C a) k ≐ entry C (monus k a) :=
      (entry_congr (.eqRefl _) (eq_add_of_le Prf.hyp0)).eqTrans
        (pad_tail C a _ (lt_congr (.eqRefl _) hC.wk.eqSymm sub))
    exact (shifted_on _ _ _ _ Prf.hyp0).eqTrans
      ((padded_inside _ _ _ sub).eqTrans decode.eqSymm)

theorem spike_at_add (a b c j : PTm n) : Γ ⊢[PRAAx] spike (a+b) c (a+j) ≐ spike b c j := by
  refine .orE (eq_or_ne j b) ?_ ?_
  · exact (spike_hit _ _ _ (congrAdd (.eqRefl _) Prf.hyp0)).eqTrans (spike_hit _ _ _ Prf.hyp0).eqSymm
  · have miss : neg (j ≐ b) :: Γ ⊢[PRAAx] neg (a+j ≐ a+b) := by
      refine .impI ?_
      have e : (a+j ≐ a+b) :: neg (j ≐ b) :: Γ ⊢[PRAAx] j ≐ b := (add_monus' j a).eqSymm.eqTrans ((congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (add_monus' b a))
      exact .impE Prf.hyp1 e
    exact (spike_miss _ _ _ miss).eqTrans (spike_miss _ _ _ Prf.hyp0).eqSymm

theorem shifted_constant (c b a k : PTm n) : Γ ⊢[PRAAx]
    shifted (constant c (succ b)) (succ b) a k ≐ spike (a+b) c k := by
  refine .orE (lt_or_le k a) ?_ ?_
  · exact (shifted_off _ _ _ _ Prf.hyp0).eqTrans
      (spike_miss _ _ _ (different_of_lt (lt_of_lt_of_le Prf.hyp0 (le_add_right a b)))).eqSymm
  · exact (shifted_on _ _ _ _ Prf.hyp0).eqTrans
      ((constant_padded _ _ _).eqTrans
        ((spike_at_add a b c (monus k a)).eqSymm.eqTrans
          (spike_congr (.eqRefl _) (.eqRefl _) (eq_add_of_le Prf.hyp0).eqSymm)))

theorem constant_congr {c c' L L' : PTm n} (hc : Γ ⊢[PRAAx] c ≐ c') (hL : Γ ⊢[PRAAx] L ≐ L') : Γ ⊢[PRAAx]
    constant c L ≐ constant c' L' := by
  ipra_congr (constant (var 0) (var 1) : PTm 2) with [hc, hL]

theorem shifted_constant_positive (c D a k : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    shifted (constant c D) D a k ≐ spike (a+pred D) c k :=
  (shifted_congr (constant_congr (.eqRefl _) (RationalIntegerNormalization.positive_form hD))
    (RationalIntegerNormalization.positive_form hD) (.eqRefl _) (.eqRefl _)).eqTrans (shifted_constant _ _ _ _)

theorem companion_balance_zero (P R D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (_hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hR : Γ ⊢[PRAAx] length R ≐ D) (hCan : Γ ⊢[PRAAx] canonicalCoefficients R) : Γ ⊢[PRAAx]
    padded R D zero ≐ qadd (qmul (GaussianRationalMonicCompanion.lead R) (padded P (succ D) zero))
      (shifted (GaussianRationalMonicCompanion.companionY P R D) D one zero) := by
  have leadCan := GaussianRationalSyntheticDivision.canonical_coefficient_at R zero hCan
    (lt_congr (.eqRefl _) hR.eqSymm hD)
  have rhs : Γ ⊢[PRAAx]
      qadd (qmul (GaussianRationalMonicCompanion.lead R) (padded P (succ D) zero))
        (shifted (GaussianRationalMonicCompanion.companionY P R D) D one zero) ≐ GaussianRationalMonicCompanion.lead R :=
    (qadd_congr (qmul_congr (.eqRefl _) ((padded_inside _ _ _ (zero_lt_succ D)).eqTrans hMonic))
      (shifted_off _ _ _ _ (le_refl one))).eqTrans
        ((GaussianRationalSumAlgebra.contextual_unit _ _).eqTrans
          (GaussianRationalLinearProduct.qadd_zero_right _ leadCan))
  exact (padded_inside R D zero hD).eqTrans rhs.eqSymm

theorem companion_balance_succ (P R D i : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ D)
    (hR : Γ ⊢[PRAAx] length R ≐ D) (hCan : Γ ⊢[PRAAx] canonicalCoefficients R) : Γ ⊢[PRAAx]
    padded R D (succ i) ≐ qadd (qmul (GaussianRationalMonicCompanion.lead R) (padded P (succ D) (succ i)))
      (shifted (GaussianRationalMonicCompanion.companionY P R D) D one (succ i)) := by
  have shiftCode : Γ ⊢[PRAAx] shifted (GaussianRationalMonicCompanion.companionY P R D) D one (succ i) ≐
      padded (GaussianRationalMonicCompanion.companionY P R D) D i :=
    (shifted_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (by ipra_ring)).eqTrans (shifted_at_add _ _ _ _)
  refine .orE (lt_or_le i D) ?_ ?_
  · have pRange : lt i D :: Γ ⊢[PRAAx] lt (succ i) (succ D) := (succ_monus_succ _ _).eqTrans Prf.hyp0
    have rhs : lt i D :: Γ ⊢[PRAAx]
        qadd (qmul (GaussianRationalMonicCompanion.lead R) (padded P (succ D) (succ i)))
          (shifted (GaussianRationalMonicCompanion.companionY P R D) D one (succ i)) ≐ padded R D (succ i) :=
      (qadd_congr (qmul_congr (.eqRefl _) (padded_inside _ _ _ pRange))
        (shiftCode.wk.eqTrans ((padded_inside _ _ _ Prf.hyp0).eqTrans
          (GaussianRationalMonicCompanion.companion_lookup P R D i hP.wk hR.wk Prf.hyp0)))).eqTrans
            (GaussianRationalLinearProduct.add_sub_right _ _ (padded_canonical R D (succ i) hR.wk hCan.wk))
    exact rhs.eqSymm
  · have rhs : le D i :: Γ ⊢[PRAAx]
        qadd (qmul (GaussianRationalMonicCompanion.lead R) (padded P (succ D) (succ i)))
          (shifted (GaussianRationalMonicCompanion.companionY P R D) D one (succ i)) ≐ qzero :=
      (qadd_congr ((qmul_congr (.eqRefl _) (padded_outside _ _ _ ((succ_monus_succ _ _).eqTrans Prf.hyp0))).eqTrans (qmul_zero_right _))
        (shiftCode.wk.eqTrans (padded_outside _ _ _ Prf.hyp0))).eqTrans zero_add_zero
    exact (padded_outside _ _ _ (le_trans Prf.hyp0 (le_succ_self _))).eqTrans rhs.eqSymm

theorem companion_balance (P R D j : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hR : Γ ⊢[PRAAx] length R ≐ D) (hCan : Γ ⊢[PRAAx] canonicalCoefficients R) : Γ ⊢[PRAAx]
    padded R D j ≐ qadd (qmul (GaussianRationalMonicCompanion.lead R) (padded P (succ D) j))
      (shifted (GaussianRationalMonicCompanion.companionY P R D) D one j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact (padded_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      ((companion_balance_zero P R D hD.wk hP.wk hMonic.wk hR.wk hCan.wk).eqTrans
        (qadd_congr (qmul_congr (.eqRefl _) (padded_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))
          (shifted_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm)))
  · exact (padded_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      ((companion_balance_succ P R D (pred j) hP.wk hR.wk hCan.wk).eqTrans
        (qadd_congr (qmul_congr (.eqRefl _) (padded_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))
          (shifted_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm)))

theorem shifted_companion_balance (P R D a k : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hR : Γ ⊢[PRAAx] length R ≐ D) (hCan : Γ ⊢[PRAAx] canonicalCoefficients R) : Γ ⊢[PRAAx]
    shifted R D a k ≐ qadd (offsetCoefficient P (GaussianRationalMonicCompanion.lead R) (succ D) a k)
      (shifted (GaussianRationalMonicCompanion.companionY P R D) D (succ a) k) := by
  refine .orE (lt_or_le k a) ?_ ?_
  · exact (shifted_off _ _ _ _ Prf.hyp0).eqTrans
      (zero_add_zero.eqSymm.eqTrans
        (qadd_congr (offset_off _ _ _ _ _ Prf.hyp0).eqSymm
          (shifted_off _ _ _ _ (lt_of_lt_of_le Prf.hyp0 (le_succ_self _))).eqSymm))
  · have comp : le a k :: Γ ⊢[PRAAx]
        shifted (GaussianRationalMonicCompanion.companionY P R D) D (succ a) k ≐
          shifted (GaussianRationalMonicCompanion.companionY P R D) D one (monus k a) :=
      (shifted_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (eq_add_of_le Prf.hyp0)).eqTrans
        (shifted_compose _ _ a one (monus k a))
    exact (shifted_on _ _ _ _ Prf.hyp0).eqTrans
      ((companion_balance P R D (monus k a) hD.wk hP.wk hMonic.wk hR.wk hCan.wk).eqTrans
        (qadd_congr (offset_on _ _ _ _ _ Prf.hyp0).eqSymm comp.eqSymm))

theorem recode_zero : Γ ⊢[PRAAx] recode (qzero : PTm n) ≐ qzero := recode_eq _ qzero_canonical

theorem padded_prefix_succ (S r j : PTm n) : Γ ⊢[PRAAx]
    recode (padded S (succ r) j) ≐ qadd (recode (padded S r j)) (spike r (entry S r) j) := by
  refine .orE (lt_or_le j r) ?_ ?_
  · have rhs : lt j r :: Γ ⊢[PRAAx] qadd (recode (padded S r j)) (spike r (entry S r) j) ≐ recode (entry S j) :=
      (qadd_congr (GaussianTranslatedNonconstant.recode_congr (padded_inside _ _ _ Prf.hyp0))
        (spike_miss _ _ _ (different_of_lt Prf.hyp0))).eqTrans
          (GaussianRationalLinearProduct.qadd_zero_right _ (recode_canonical _))
    exact (GaussianTranslatedNonconstant.recode_congr (padded_inside _ _ _ (lt_of_lt_of_le Prf.hyp0 (le_succ_self _)))).eqTrans rhs.eqSymm
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · have rhs : lt r j :: le r j :: Γ ⊢[PRAAx] qadd (recode (padded S r j)) (spike r (entry S r) j) ≐ qzero :=
        (qadd_congr ((GaussianTranslatedNonconstant.recode_congr (padded_outside _ _ _ (le_of_lt Prf.hyp0))).eqTrans recode_zero)
          (spike_miss _ _ _ (different_of_gt Prf.hyp0))).eqTrans zero_add_zero
      exact ((GaussianTranslatedNonconstant.recode_congr (padded_outside _ _ _ Prf.hyp0)).eqTrans recode_zero).eqTrans rhs.eqSymm
    · have rhs : (r ≐ j) :: le r j :: Γ ⊢[PRAAx] qadd (recode (padded S r j)) (spike r (entry S r) j) ≐ recode (entry S r) :=
        qadd_congr ((GaussianTranslatedNonconstant.recode_congr (padded_outside _ _ _ Prf.hyp1)).eqTrans recode_zero)
          (spike_hit _ _ _ Prf.hyp0.eqSymm)
      have range : (r ≐ j) :: le r j :: Γ ⊢[PRAAx] lt j (succ r) := lt_congr Prf.hyp0 (.eqRefl _) (le_refl (succ r))
      exact (GaussianTranslatedNonconstant.recode_congr
        ((padded_inside _ _ _ range).eqTrans (entry_congr (.eqRefl _) Prf.hyp0.eqSymm))).eqTrans rhs.eqSymm

theorem spike_local_global (a b c k : PTm n) (ha : Γ ⊢[PRAAx] le a k) : Γ ⊢[PRAAx]
    spike b c (monus k a) ≐ spike (a+b) c k :=
  (spike_at_add a b c (monus k a)).eqSymm.eqTrans
    (spike_congr (.eqRefl _) (.eqRefl _) (eq_add_of_le ha).eqSymm)

theorem shifted_prefix_succ (S r a k : PTm n) : Γ ⊢[PRAAx]
    recode (shifted S (succ r) a k) ≐ qadd (recode (shifted S r a k)) (spike (a+r) (entry S r) k) := by
  refine .orE (lt_or_le k a) ?_ ?_
  · have rhs : lt k a :: Γ ⊢[PRAAx] qadd (recode (shifted S r a k)) (spike (a+r) (entry S r) k) ≐ qzero :=
      (qadd_congr ((GaussianTranslatedNonconstant.recode_congr (shifted_off _ _ _ _ Prf.hyp0)).eqTrans recode_zero)
        (spike_miss _ _ _ (different_of_lt (lt_of_lt_of_le Prf.hyp0 (le_add_right _ _))))).eqTrans zero_add_zero
    exact ((GaussianTranslatedNonconstant.recode_congr (shifted_off _ _ _ _ Prf.hyp0)).eqTrans recode_zero).eqTrans rhs.eqSymm
  · exact (GaussianTranslatedNonconstant.recode_congr (shifted_on _ _ _ _ Prf.hyp0)).eqTrans
      ((padded_prefix_succ _ _ _).eqTrans
        (qadd_congr (GaussianTranslatedNonconstant.recode_congr (shifted_on _ _ _ _ Prf.hyp0).eqSymm)
          (spike_local_global a r (entry S r) k Prf.hyp0)))

theorem remainder_next_shifted (P R D a r k : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    shifted (remainderNext P R D a) D (succ (succ r)) k ≐
      qadd (shifted (GaussianRationalMonicCompanion.companionY P R D) D (succ (succ r)) k)
        (spike (succ D+r) a k) := by
  have target : Γ ⊢[PRAAx] succ (succ r)+pred D ≐ succ D+r :=
    ((congrAdd (congrSucc (RationalIntegerNormalization.positive_form hD)) (.eqRefl r)).eqTrans (by ipra_ring)).eqSymm
  exact (shifted_added _ _ _ _ _).eqTrans
    (qadd_congr (.eqRefl _) ((shifted_constant_positive _ _ _ _ hD).eqTrans
      (spike_congr target (.eqRefl _) (.eqRefl _))))

theorem coefficient_right_congr (P M t k : PTm n) {Q Q' : PTm n} (hQ : Γ ⊢[PRAAx] Q ≐ Q') : Γ ⊢[PRAAx]
    coefficient P Q M t k ≐ coefficient P Q' M t k :=
  GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialProduct.contributionBody (.eqRefl _)
    (congrPairT (.eqRefl _) (congrPairT hQ (.eqRefl _)))

theorem coefficient_zeros (P M t k : PTm n) : Γ ⊢[PRAAx]
    coefficient P (GaussianRationalPolynomialBuffers.zeros (succ M)) M t k ≐ qzero := by
  have eqs : Γ ⊢[PRAAx]
      GaussianRationalFiniteSum.termsEqual GaussianRationalPolynomialProduct.contributionBody (qzero : PTm 2)
        t (GaussianRationalPolynomialProduct.data P (GaussianRationalPolynomialBuffers.zeros (succ M)) M k) zero := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift t) :: Γ.map Fm.shift
    have value : Δ ⊢[PRAAx] contribution (Syn.shift P) (GaussianRationalPolynomialBuffers.zeros (succ (Syn.shift M)))
        (Syn.shift M) (Syn.shift k) (var 0) ≐ qzero := by
      refine .orE (le_or_lt (var 0) (Syn.shift k)) ?_ ?_
      · exact (contribution_inside _ _ _ _ _ Prf.hyp0).eqTrans
          ((qmul_congr (.eqRefl _) (padded_zeros _ _)).eqTrans (qmul_zero_right _))
      · exact contribution_outside _ _ _ _ _ Prf.hyp0
    simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_data,GaussianRationalPolynomialBuffers.subst_zeros,
      ConciseIPRA.PTm.subst_succ,inst2,GaussianRationalHorner.subst_qzero] using
        (GaussianRationalPolynomialProduct.contribution_body_at _ _ _ _ _).eqTrans value
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ eqs).eqTrans (GaussianRationalPolynomialProduct.constant_zero_sum _ _)

def rowLaw (P S D k r : PTm n) : Fm PTm n :=
  recode (shifted S r (succ D) k) ≐
    qadd (coefficient P (quotient P S D r) r (succ D) k) (shifted (remainder P S D r) D (succ r) k)
@[simp] theorem subst_rowLaw {l : ℕ} (σ : Fin n → PTm l) (P S D k r : PTm n) :
    (rowLaw P S D k r).subst σ = rowLaw (Syn.subst σ P) (Syn.subst σ S) (Syn.subst σ D)
      (Syn.subst σ k) (Syn.subst σ r) := by simp [rowLaw]

theorem reconstruction_shuffle (a b c d : PTm n) : Γ ⊢[PRAAx]
    qadd (qadd a b) (qadd c d) ≐ qadd (qadd a (qadd b c)) d :=
  (GaussianRationalSumAlgebra.qadd_associative (qadd a b) c d).eqSymm.eqTrans
    (qadd_congr (GaussianRationalSumAlgebra.qadd_associative a b c) (.eqRefl _))

/-- A coefficient index remains a numerical parameter of the genuine QF
prefix induction. Explicit padding makes its step valid even outside the
current prefix, so no quantified induction or global row law is assumed. -/
theorem prefix_reconstruction (P S D k r : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone) : Γ ⊢[PRAAx]
    rowLaw P S D k r := by
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by
    simpa only [Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hD.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift P) ≐ succ (Syn.shift D) := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,Syn.shift,ConciseIPRA.PTm.subst_succ] using hP.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] entry (Syn.shift P) zero ≐ qone := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.MasterCertificate.subst_entry,Syn.shift,ConciseIPRA.PTm.subst_zero,
      GaussianRationalSyntheticDivision.subst_qone] using hMonic.shift
  have all : Γ ⊢[PRAAx] .all (rowLaw (Syn.shift P) (Syn.shift S) (Syn.shift D) (Syn.shift k) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_rowLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have left : Γ ⊢[PRAAx] recode (shifted S zero (succ D) k) ≐ qzero :=
        (GaussianTranslatedNonconstant.recode_congr (shifted_empty S _ _)).eqTrans recode_zero
      have right : Γ ⊢[PRAAx]
          qadd (coefficient P (quotient P S D zero) zero (succ D) k) (shifted (remainder P S D zero) D one k) ≐ qzero :=
        (qadd_congr ((coefficient_right_congr P _ _ _ (GaussianRationalMonicReduction.quotient_zero P S D)).eqTrans
          (coefficient_zeros _ _ _ _))
          ((shifted_congr (GaussianRationalMonicReduction.remainder_zero P S D) (.eqRefl _) (.eqRefl _) (.eqRefl _)).eqTrans
            (shifted_zeros _ _ _))).eqTrans zero_add_zero
      exact left.eqTrans right.eqSymm
    · simp only [subst_rowLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let Δ := rowLaw (Syn.shift P) (Syn.shift S) (Syn.shift D) (Syn.shift k) (var 0) :: Γ.map Fm.shift
      have qstep : Δ ⊢[PRAAx]
          coefficient (Syn.shift P) (quotient (Syn.shift P) (Syn.shift S) (Syn.shift D) (succ (var 0)))
            (succ (var 0)) (succ (Syn.shift D)) (Syn.shift k) ≐
          qadd (coefficient (Syn.shift P) (quotient (Syn.shift P) (Syn.shift S) (Syn.shift D) (var 0))
            (var 0) (succ (Syn.shift D)) (Syn.shift k))
            (offsetCoefficient (Syn.shift P) (GaussianRationalMonicCompanion.lead
              (remainder (Syn.shift P) (Syn.shift S) (Syn.shift D) (var 0))) (succ (Syn.shift D)) (succ (var 0)) (Syn.shift k)) :=
        (coefficient_right_congr _ _ _ _ (GaussianRationalMonicReduction.quotient_succ _ _ _ _)).eqTrans
          (coefficient_quotient_next _ _ _ _ _ _ (GaussianRationalMonicReduction.quotient_length _ _ _ _))
      have rstep := (shifted_congr (Γ := Δ) (GaussianRationalMonicReduction.remainder_succ
          (Syn.shift P) (Syn.shift S) (Syn.shift D) (var 0)) (.eqRefl (Syn.shift D)) (.eqRefl (succ (succ (var 0)))) (.eqRefl (Syn.shift k))).eqTrans
        (remainder_next_shifted _ _ _ _ (var 0) (Syn.shift k) ds.wk)
      have balance := shifted_companion_balance (Γ := Δ) (Syn.shift P)
        (remainder (Syn.shift P) (Syn.shift S) (Syn.shift D) (var 0)) (Syn.shift D) (succ (var 0)) (Syn.shift k)
        ds.wk ps.wk ms.wk (GaussianRationalMonicReduction.remainder_length _ _ _ _)
        (GaussianRationalMonicReduction.remainder_canonical _ _ _ _)
      have rhs := (qadd_congr qstep rstep).eqTrans
        ((reconstruction_shuffle _ _ _ _).eqTrans
          ((qadd_congr (qadd_congr (.eqRefl _) balance.eqSymm) (.eqRefl _)).eqTrans
            ((qadd_congr (Prf.hyp0 : Δ ⊢[PRAAx] rowLaw (Syn.shift P) (Syn.shift S) (Syn.shift D) (Syn.shift k) (var 0)).eqSymm (.eqRefl _)).eqTrans
              (shifted_prefix_succ (Syn.shift S) (var 0) (succ (Syn.shift D)) (Syn.shift k)).eqSymm)))
      exact rhs.eqSymm
  simpa only [subst_rowLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

def width (D M : PTm n) : PTm n := succ (D+succ M)
def outputQuotient (P S D M : PTm n) : PTm n := fstT (GaussianRationalMonicReduction.run P S D M)
def outputRemainder (P S D M : PTm n) : PTm n := sndT (GaussianRationalMonicReduction.run P S D M)
def paddedInput (S D : PTm n) : PTm n := leftPad S (succ D)
def productPart (P S D M : PTm n) : PTm n := GaussianRationalPolynomialProduct.product P (outputQuotient P S D M) D (succ M)
def remainderPart (P S D M : PTm n) : PTm n := leftPad (outputRemainder P S D M) (succ (succ M))
def reconstructed (P S D M : PTm n) : PTm n := added (productPart P S D M) (remainderPart P S D M) (width D M)
@[simp] theorem subst_width {l : ℕ} (σ : Fin n → PTm l) (D M : PTm n) :
    Syn.subst σ (width D M) = width (Syn.subst σ D) (Syn.subst σ M) := by simp [width]
@[simp] theorem subst_outputQuotient {l : ℕ} (σ : Fin n → PTm l) (P S D M : PTm n) :
    Syn.subst σ (outputQuotient P S D M) = outputQuotient (Syn.subst σ P) (Syn.subst σ S) (Syn.subst σ D) (Syn.subst σ M) := by simp [outputQuotient]
@[simp] theorem subst_outputRemainder {l : ℕ} (σ : Fin n → PTm l) (P S D M : PTm n) :
    Syn.subst σ (outputRemainder P S D M) = outputRemainder (Syn.subst σ P) (Syn.subst σ S) (Syn.subst σ D) (Syn.subst σ M) := by simp [outputRemainder]
@[simp] theorem subst_paddedInput {l : ℕ} (σ : Fin n → PTm l) (S D : PTm n) :
    Syn.subst σ (paddedInput S D) = paddedInput (Syn.subst σ S) (Syn.subst σ D) := by simp [paddedInput]
@[simp] theorem subst_productPart {l : ℕ} (σ : Fin n → PTm l) (P S D M : PTm n) :
    Syn.subst σ (productPart P S D M) = productPart (Syn.subst σ P) (Syn.subst σ S) (Syn.subst σ D) (Syn.subst σ M) := by simp [productPart]
@[simp] theorem subst_remainderPart {l : ℕ} (σ : Fin n → PTm l) (P S D M : PTm n) :
    Syn.subst σ (remainderPart P S D M) = remainderPart (Syn.subst σ P) (Syn.subst σ S) (Syn.subst σ D) (Syn.subst σ M) := by simp [remainderPart]
@[simp] theorem subst_reconstructed {l : ℕ} (σ : Fin n → PTm l) (P S D M : PTm n) :
    Syn.subst σ (reconstructed P S D M) = reconstructed (Syn.subst σ P) (Syn.subst σ S) (Syn.subst σ D) (Syn.subst σ M) := by simp [reconstructed]

/-- Actual coefficient reconstruction of the original input, using the SAME
returned PR4 quotient and remainder and the actual convolution product. -/
theorem coefficient_identity (P S D M i : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hS : Γ ⊢[PRAAx] length S ≐ succ M) (hi : Γ ⊢[PRAAx] lt i (width D M)) : Γ ⊢[PRAAx]
    recode (entry (paddedInput S D) i) ≐ qadd (entry (productPart P S D M) i) (entry (remainderPart P S D M) i) := by
  have sourceRange : Γ ⊢[PRAAx] lt i (succ D+succ M) := le_congr (.eqRefl _) (by unfold width; ipra_ring) hi
  have remainderRange : Γ ⊢[PRAAx] lt i (succ (succ M)+D) := le_congr (.eqRefl _) (by unfold width; ipra_ring) hi
  have productRange : Γ ⊢[PRAAx] le i (D+succ M) := (succ_monus_succ _ _).eqSymm.eqTrans hi
  have sourceCode := GaussianTranslatedNonconstant.recode_congr (shifted_pad_entry S (succ M) (succ D) i hS sourceRange)
  have productCode : Γ ⊢[PRAAx] coefficient P (quotient P S D (succ M)) (succ M) (succ D) i ≐ entry (productPart P S D M) i :=
    (coefficient_right_congr P _ _ _ (GaussianRationalMonicReduction.returned_quotient P S D M).eqSymm).eqTrans
      (GaussianRationalPolynomialProduct.product_lookup P (outputQuotient P S D M) D (succ M) i productRange).eqSymm
  have remainderCode : Γ ⊢[PRAAx] shifted (remainder P S D (succ M)) D (succ (succ M)) i ≐ entry (remainderPart P S D M) i :=
    (shifted_pad_entry _ _ _ _ (GaussianRationalMonicReduction.remainder_length _ _ _ _) remainderRange).eqTrans
      (entry_congr (leftPad_congr (GaussianRationalMonicReduction.returned_remainder P S D M).eqSymm (.eqRefl _)) (.eqRefl _))
  exact sourceCode.eqSymm.eqTrans ((prefix_reconstruction P S D i (succ M) hD hP hMonic).eqTrans
    (qadd_congr productCode remainderCode))

theorem reconstructed_lookup (P S D M i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width D M)) : Γ ⊢[PRAAx]
    entry (reconstructed P S D M) i ≐ qadd (entry (productPart P S D M) i) (entry (remainderPart P S D M) i) :=
  added_lookup _ _ _ _ hi

theorem reconstructed_coefficient (P S D M i : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hS : Γ ⊢[PRAAx] length S ≐ succ M) (hi : Γ ⊢[PRAAx] lt i (width D M)) : Γ ⊢[PRAAx]
    recode (entry (paddedInput S D) i) ≐ entry (reconstructed P S D M) i :=
  (coefficient_identity P S D M i hD hP hMonic hS hi).eqTrans (reconstructed_lookup P S D M i hi).eqSymm

theorem input_length (S D M : PTm n) (hS : Γ ⊢[PRAAx] length S ≐ succ M) : Γ ⊢[PRAAx]
    length (paddedInput S D) ≐ width D M :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) hS).eqTrans (by unfold width; ipra_ring))
theorem product_length (P S D M : PTm n) : Γ ⊢[PRAAx] length (productPart P S D M) ≐ width D M :=
  GaussianRationalPolynomialProduct.product_length _ _ _ _
theorem remainder_length (P S D M : PTm n) : Γ ⊢[PRAAx] length (remainderPart P S D M) ≐ width D M :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (GaussianRationalMonicReduction.returned_remainder_length _ _ _ _)).eqTrans (by unfold width; ipra_ring))
theorem reconstructed_length (P S D M : PTm n) : Γ ⊢[PRAAx] length (reconstructed P S D M) ≐ width D M := added_length _ _ _
theorem reconstructed_canonical (P S D M : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (reconstructed P S D M) :=
  GaussianRationalMonicReduction.added_canonical _ _ _

def reconstructionF : PR 4 := PTm.toPR (reconstructed (var 0) (var 1) (var 2) (var 3))
def reconstructionRun (P S D M : PTm n) : PTm n := PTm.app reconstructionF ![P,S,D,M]
@[simp] theorem subst_reconstructionRun {l : ℕ} (σ : Fin n → PTm l) (P S D M : PTm n) :
    Syn.subst σ (reconstructionRun P S D M) = reconstructionRun (Syn.subst σ P) (Syn.subst σ S) (Syn.subst σ D) (Syn.subst σ M) := by
  simp only [reconstructionRun,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem reconstruction_program_at (P S D M : PTm n) : Γ ⊢[PRAAx] reconstructionRun P S D M ≐ reconstructed P S D M := by
  simpa only [reconstructionRun,reconstructionF,subst_reconstructed,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (reconstructed (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,S,D,M]
theorem returned_coefficient (P S D M i : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hP : Γ ⊢[PRAAx] length P ≐ succ D) (hMonic : Γ ⊢[PRAAx] entry P zero ≐ qone)
    (hS : Γ ⊢[PRAAx] length S ≐ succ M) (hi : Γ ⊢[PRAAx] lt i (width D M)) : Γ ⊢[PRAAx]
    recode (entry (paddedInput S D) i) ≐ entry (reconstructionRun P S D M) i :=
  (reconstructed_coefficient P S D M i hD hP hMonic hS hi).eqTrans
    (entry_congr (reconstruction_program_at P S D M).eqSymm (.eqRefl _))

theorem actual_prefix_coefficient_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶
      rowLaw (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (prefix_reconstruction _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_monic_coefficient_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶ length (var 1) ≐ succ (var 3) ⟶
      lt (var 4) (width (var 2) (var 3)) ⟶ recode (entry (paddedInput (var 1) (var 2)) (var 4)) ≐
        qadd (entry (productPart (var 0) (var 1) (var 2) (var 3)) (var 4)) (entry (remainderPart (var 0) (var 1) (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI (coefficient_identity _ _ _ _ _ hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))
theorem actual_reconstructed_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶ length (var 1) ≐ succ (var 3) ⟶
      lt (var 4) (width (var 2) (var 3)) ⟶ recode (entry (paddedInput (var 1) (var 2)) (var 4)) ≐
        entry (reconstructed (var 0) (var 1) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI (reconstructed_coefficient _ _ _ _ _ hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))
theorem actual_reconstruction_shapes_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 1) ≐ succ (var 3) ⟶
      ((length (paddedInput (var 1) (var 2)) ≐ width (var 2) (var 3)) ⋏
        ((length (productPart (var 0) (var 1) (var 2) (var 3)) ≐ width (var 2) (var 3)) ⋏
          ((length (remainderPart (var 0) (var 1) (var 2) (var 3)) ≐ width (var 2) (var 3)) ⋏
            (length (reconstructed (var 0) (var 1) (var 2) (var 3)) ≐ width (var 2) (var 3)))))) :=
  closeUniv 4 (.impI (.andI (input_length _ _ _ Prf.hyp0) (.andI (product_length _ _ _ _)
    (.andI (remainder_length _ _ _ _) (reconstructed_length _ _ _ _)))))
theorem actual_reconstruction_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((reconstructionRun (var 0) (var 1) (var 2) (var 3) ≐ reconstructed (var 0) (var 1) (var 2) (var 3)) ⋏
      canonicalCoefficients (reconstructed (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (reconstruction_program_at _ _ _ _) (reconstructed_canonical _ _ _ _))
theorem actual_returned_coefficient_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ length (var 0) ≐ succ (var 2) ⟶ entry (var 0) zero ≐ qone ⟶ length (var 1) ≐ succ (var 3) ⟶
      lt (var 4) (width (var 2) (var 3)) ⟶ recode (entry (paddedInput (var 1) (var 2)) (var 4)) ≐
        entry (reconstructionRun (var 0) (var 1) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI (returned_coefficient _ _ _ _ _ hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianRationalMonicReconstruction
