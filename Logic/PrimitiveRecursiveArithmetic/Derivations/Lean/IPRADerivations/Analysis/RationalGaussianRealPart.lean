import IPRADerivations.Analysis.RationalGaussianEmbedding
import IPRADerivations.Analysis.GaussianRationalFiniteSum

/-!
# Real parts and original rational finite sums

An arbitrary Gaussian coefficient may multiply an embedded rational entry.
Its real part is the original rational product of the real part and entry.
Actual finite sums commute with this projection. No assumption that the
Gaussian coefficient itself is real is made.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalGaussianRealPart

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed scalarZero native embed_represents)
open RationalSupMetric (numeratorOf denominatorOf)
open GaussianRationalHorner (qzero qadd qmul)
open GaussianRationalL1 (rawDen rawGaussian raw_represents raw_den_positive)
open GaussianRootAlgebra (re_mul im_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem scalar_zero_integer : Γ ⊢[PRAAx] (scalarZero : PTm n) ≐
    RationalIntegerNormalization.integerCode (ZT.natLit 0) := by
  apply RationalIntegerNormalization.normalize_integer _ _ _ (le_refl one)
  apply ZT.derive
  simp [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_natLit]

theorem rational_sum_zero (t : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] RationalFiniteSum.sum t zero x ≐ scalarZero :=
  (RationalFiniteSum.sum_zero t x).eqTrans scalar_zero_integer.eqSymm

theorem real_zero : Γ ⊢[PRAAx] fstT (qzero : PTm n) ≐ scalarZero :=
  ((congrFst RationalGaussianEmbedding.embed_zero).eqSymm.eqTrans (fst_pair _ _)).eqTrans
    RationalGaussianEmbedding.scalar_recode_zero

theorem real_add (a b : PTm n) : Γ ⊢[PRAAx]
    fstT (qadd a b) ≐ RationalArithmetic.add (fstT a) (fstT b) := fst_pair _ _

theorem real_product (a b : PTm n) : Γ ⊢[PRAAx]
    fstT (qmul a (embed b)) ≐ RationalArithmetic.multiply (fstT a) b := by
  have hv := GaussianRationalHorner.qmul_represents (Γ := Γ) a (embed b) (rawGaussian a)
    (native (numeratorOf b)) (rawDen a) (denominatorOf b) (raw_den_positive a)
    (RationalArgmin.denominator_positive b) (raw_represents a) (embed_represents b)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (Prf.andE₁ (Prf.andE₂ (GaussianRationalHorner.qmul_canonical _ _)))
    (RationalArithmetic.multiply_guard _ _) (Prf.andE₁ hv) (RationalArithmetic.multiply_value _ _)
    (GaussianRationalHorner.positive_product _ _ (raw_den_positive a) (RationalArgmin.denominator_positive b))
    (RationalArithmetic.product_denominator_positive _ _)
  apply ZT.derive
  simp only [re_mul,native,rawGaussian,rawDen,RationalArithmetic.productDenominator,
    ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
    ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem real_values (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalValueEquality.valueEqual a b) :
    Γ ⊢[PRAAx] RationalArgmin.rationalEq (fstT a) (fstT b) := by
  have e := GaussianRationalValueEquality.recode_equal_of_equal_values a b h
  have ea := (congrFst (RationalGaussianEmbedding.recode_pair (Γ := Γ) a)).eqTrans (fst_pair _ _)
  have eb := (congrFst (RationalGaussianEmbedding.recode_pair (Γ := Γ) b)).eqTrans (fst_pair _ _)
  exact RationalGaussianEmbedding.rational_equal_of_scalar_recode _ _
    (ea.eqSymm.eqTrans ((congrFst e).eqTrans eb))

def realBody (t : PTm 2) : PTm 2 := fstT t
def embedBody (t : PTm 2) : PTm 2 := embed t
def realSumLaw (t : PTm 2) (N x : PTm n) : Fm PTm n :=
  fstT (GaussianRationalFiniteSum.sum t N x) ≐ RationalFiniteSum.sum (realBody t) N x
def embedSumLaw (t : PTm 2) (N x : PTm n) : Fm PTm n :=
  embed (RationalFiniteSum.sum t N x) ≐ GaussianRationalFiniteSum.sum (embedBody t) N x
@[simp] theorem subst_realSumLaw {l : ℕ} (σ : Fin n → PTm l) (t : PTm 2) (N x : PTm n) :
    (realSumLaw t N x).subst σ = realSumLaw t (Syn.subst σ N) (Syn.subst σ x) := by simp [realSumLaw]
@[simp] theorem subst_embedSumLaw {l : ℕ} (σ : Fin n → PTm l) (t : PTm 2) (N x : PTm n) :
    (embedSumLaw t N x).subst σ = embedSumLaw t (Syn.subst σ N) (Syn.subst σ x) := by simp [embedSumLaw]

theorem real_sum_step (t : PTm 2) (N x : PTm n)
    (ih : Γ ⊢[PRAAx] fstT (GaussianRationalFiniteSum.sum t N x) ≐ RationalFiniteSum.sum (realBody t) N x) :
    Γ ⊢[PRAAx] fstT (GaussianRationalFiniteSum.sum t (succ N) x) ≐ RationalFiniteSum.sum (realBody t) (succ N) x := by
  have termEq : Γ ⊢[PRAAx] fstT (inst2 t N x) ≐ RationalFiniteSum.term (realBody t) N x := by
    simp only [RationalFiniteSum.term,realBody,inst2,subst_fstT]
    exact .eqRefl _
  exact ((congrFst (GaussianRationalFiniteSum.sum_succ t N x)).eqTrans (real_add _ _)).eqTrans
    ((RationalAlgebra.add_congr ih termEq).eqTrans (RationalFiniteSum.sum_succ (realBody t) N x).eqSymm)

theorem real_sum (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    fstT (GaussianRationalFiniteSum.sum t N x) ≐ RationalFiniteSum.sum (realBody t) N x := by
  have all : Γ ⊢[PRAAx] .all (realSumLaw t (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simp only [subst_realSumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact ((congrFst (GaussianRationalFiniteSum.sum_zero t x)).eqTrans real_zero).eqTrans
        (rational_sum_zero (realBody t) x).eqSymm
    · simp only [subst_realSumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact real_sum_step t (var 0) (Syn.shift x) Prf.hyp0
  change Γ ⊢[PRAAx] realSumLaw t N x
  simpa only [subst_realSumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem embed_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] embed a ≐ embed b :=
  (RationalGaussianEmbedding.embed_at a).eqSymm.eqTrans
    ((congrAp1 RationalGaussianEmbedding.embedF h).eqTrans (RationalGaussianEmbedding.embed_at b))

theorem embed_sum_step (t : PTm 2) (N x : PTm n)
    (ih : Γ ⊢[PRAAx] embed (RationalFiniteSum.sum t N x) ≐ GaussianRationalFiniteSum.sum (embedBody t) N x) :
    Γ ⊢[PRAAx] embed (RationalFiniteSum.sum t (succ N) x) ≐ GaussianRationalFiniteSum.sum (embedBody t) (succ N) x := by
  have termEq : Γ ⊢[PRAAx] embed (RationalFiniteSum.term t N x) ≐ inst2 (embedBody t) N x := by
    simp only [RationalFiniteSum.term,embedBody,inst2,RationalGaussianEmbedding.subst_embed]
    exact .eqRefl _
  exact (embed_congr (RationalFiniteSum.sum_succ t N x)).eqTrans
    ((RationalGaussianEmbedding.embed_add _ _).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr ih termEq).eqTrans
        (GaussianRationalFiniteSum.sum_succ (embedBody t) N x).eqSymm))

theorem embed_sum (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    embed (RationalFiniteSum.sum t N x) ≐ GaussianRationalFiniteSum.sum (embedBody t) N x := by
  have all : Γ ⊢[PRAAx] .all (embedSumLaw t (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simp only [subst_embedSumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (embed_congr (rational_sum_zero t x)).eqTrans
        (RationalGaussianEmbedding.embed_zero.eqTrans (GaussianRationalFiniteSum.sum_zero (embedBody t) x).eqSymm)
    · simp only [subst_embedSumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact embed_sum_step t (var 0) (Syn.shift x) Prf.hyp0
  change Γ ⊢[PRAAx] embedSumLaw t N x
  simpa only [subst_embedSumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem actual_real_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (fstT (qmul (var 0) (embed (var 1))) ≐ RationalArithmetic.multiply (fstT (var 0)) (var 1)) :=
  closeUniv 2 (real_product _ _)
theorem actual_real_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalValueEquality.valueEqual (var 0) (var 1) ⟶ RationalArgmin.rationalEq (fstT (var 0)) (fstT (var 1))) :=
  closeUniv 2 (.impI (real_values _ _ Prf.hyp0))
theorem actual_real_sum_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (fstT (GaussianRationalFiniteSum.sum t (var 0) (var 1)) ≐ RationalFiniteSum.sum (realBody t) (var 0) (var 1)) :=
  closeUniv 2 (real_sum t _ _)
theorem actual_embed_sum_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (RationalFiniteSum.sum t (var 0) (var 1)) ≐ GaussianRationalFiniteSum.sum (embedBody t) (var 0) (var 1)) :=
  closeUniv 2 (embed_sum t _ _)

end LeanProofs.IPRA.Analysis.RationalGaussianRealPart
