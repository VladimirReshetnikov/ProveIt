import IPRADerivations.Analysis.RationalArithmetic.Spans.RationalRowSpanGaussianEmbedding
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarDeterminant

/-!
# Original rational runtime determinants and their Gaussian embedding

The rational producer uses original rational multiplication and finite sums
on the same retained numerical permutation-word scan as the Gaussian
determinant. Conjugacy is proved for the actual signs, products, and fold;
the rational determinant is not defined by projection of a Gaussian output.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalScalarDeterminantGaussianEmbedding

open_ipra
open RationalGaussianEmbedding (embed scalarZero scalarOne)
open RationalGaussianRealPart (embedBody embed_congr)
open GaussianRationalHorner (qzero qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianPolynomialDeterminantTerms (cell signPoint)
open RationalRowSpanGaussianEmbedding (matrix matrix_lookup)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (count parity digit)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def productStep (t : PTm 2) : PTm 3 := RationalArithmetic.multiply (var 1) (inst2 t (var 0) (var 2))
def productF (t : PTm 2) : PR 2 := rec2 (scalarOne : PTm 1) (productStep t)
def product (t : PTm 2) (N x : PTm n) : PTm n := ap2 (productF t) N x
ipra_subst product

theorem product_zero (t : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] product t zero x ≐ scalarOne := by
  simpa only [product,productF,RationalGaussianEmbedding.subst_scalarOne] using
    rec2_zero (Γ := Γ) (scalarOne : PTm 1) (productStep t) x
theorem product_succ (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    product t (succ N) x ≐ RationalArithmetic.multiply (product t N x) (inst2 t N x) := by
  simpa only [product,productF,productStep,RationalArithmetic.subst_multiply,subst_inst2,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      rec2_succ (Γ := Γ) (scalarOne : PTm 1) (productStep t) N x

def productLaw (t : PTm 2) (N x : PTm n) : Fm PTm n :=
  embed (product t N x) ≐ GaussianRationalFiniteProduct.qprod (embedBody t) N x
ipra_subst productLaw

theorem product_embedding_step (t : PTm 2) (N x : PTm n)
    (ih : Γ ⊢[PRAAx] productLaw t N x) : Γ ⊢[PRAAx] productLaw t (succ N) x := by
  have termEq : Γ ⊢[PRAAx] embed (inst2 t N x) ≐ inst2 (embedBody t) N x := by
    simp only [embedBody,inst2,RationalGaussianEmbedding.subst_embed]
    exact .eqRefl _
  exact (embed_congr (product_succ t N x)).eqTrans
    ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans
      ((qmul_congr ih termEq).eqTrans (GaussianRationalFiniteProduct.product_succ (embedBody t) N x).eqSymm))

theorem product_embedding (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    embed (product t N x) ≐ GaussianRationalFiniteProduct.qprod (embedBody t) N x := by
  have all : Γ ⊢[PRAAx] .all (productLaw t (var 0) (Syn.shift x)) := by
    ipra_qfind (by trivial) [subst_productLaw]
    · exact (embed_congr (product_zero t x)).eqTrans
        (RationalGaussianEmbedding.embed_one.eqTrans (GaussianRationalFiniteProduct.product_zero (embedBody t) x).eqSymm)
    · exact product_embedding_step t (var 0) (Syn.shift x) Prf.hyp0
  change Γ ⊢[PRAAx] productLaw t N x
  simpa only [subst_productLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

def sign (m w : PTm n) : PTm n := Foundations.GuardedTotalization.sel (parity m w)
  (RationalArithmetic.negative scalarOne) scalarOne
def rawProduct (A m w : PTm n) : PTm n := product GaussianScalarDeterminant.factorBody m
  (GaussianScalarDeterminant.factorData A m w)
def signedTerm (A m t : PTm n) : PTm n := RationalArithmetic.multiply
  (sign m (GaussianPolynomialDeterminant.wordCode m t))
  (rawProduct A m (GaussianPolynomialDeterminant.wordCode m t))
def signedBody : PTm 2 := signedTerm (fstT (var 1)) (sndT (var 1)) (var 0)
def determinant (A m : PTm n) : PTm n := RationalFiniteSum.sum signedBody (count m) (pairT A m)

ipra_subst sign
ipra_subst rawProduct
ipra_subst signedTerm
ipra_subst determinant

theorem sign_even (m w : PTm n) (h : Γ ⊢[PRAAx] parity m w ≐ zero) :
    Γ ⊢[PRAAx] sign m w ≐ scalarOne := Foundations.GuardedTotalization.sel_zero h
theorem sign_odd (m w : PTm n) (h : Γ ⊢[PRAAx] parity m w ≐ one) :
    Γ ⊢[PRAAx] sign m w ≐ RationalArithmetic.negative scalarOne := Foundations.GuardedTotalization.sel_one h
theorem sign_embedding (m w : PTm n) : Γ ⊢[PRAAx] embed (sign m w) ≐ signPoint m w := by
  refine .orE (Foundations.RuntimePermutationWords.parity_cases m w) ?_ ?_
  · exact (embed_congr (sign_even m w Prf.hyp0)).eqTrans
      (RationalGaussianEmbedding.embed_one.eqTrans (GaussianPolynomialDeterminantTerms.sign_even m w Prf.hyp0).eqSymm)
  · exact (embed_congr (sign_odd m w Prf.hyp0)).eqTrans
      ((RationalGaussianEmbedding.embed_negative _).eqTrans
        ((RationalGaussianEmbedding.negative_congr RationalGaussianEmbedding.embed_one).eqTrans
          (GaussianPolynomialDeterminantTerms.sign_odd m w Prf.hyp0).eqSymm))

theorem product_matrix_embedding (A m w : PTm n) : Γ ⊢[PRAAx]
    embed (rawProduct A m w) ≐ GaussianScalarDeterminant.rawProduct (matrix A m m) m w := by
  refine (product_embedding GaussianScalarDeterminant.factorBody m (GaussianScalarDeterminant.factorData A m w)).eqTrans
    (GaussianRationalFiniteProduct.product_congr_bounded _ _ m _ _ ?_)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have lo : Δ ⊢[PRAAx]
      embed (inst2 GaussianScalarDeterminant.factorBody (var 0)
        (GaussianScalarDeterminant.factorData (Syn.shift A) (Syn.shift m) (Syn.shift w))) ≐
      embed (cell (Syn.shift A) (digit (Syn.shift m) (Syn.shift w) (var 0)) (var 0)) :=
    embed_congr (GaussianScalarDeterminant.factor_body_at _ _ _ _)
  have hi := (GaussianScalarDeterminant.factor_body_at (Γ := Δ)
    (matrix (Syn.shift A) (Syn.shift m) (Syn.shift m)) (Syn.shift m) (Syn.shift w) (var 0)).eqTrans
      (matrix_lookup _ _ _ _ _ (Foundations.RuntimePermutationWords.digit_bound _ _ _ Prf.hyp0) Prf.hyp0)
  simpa only [Δ,Syn.shift,embedBody,inst2,RationalGaussianEmbedding.subst_embed,
    GaussianScalarDeterminant.subst_factorData,RationalRowSpanGaussianEmbedding.subst_matrix] using lo.eqTrans hi.eqSymm

theorem signed_term_embedding (A m t : PTm n) : Γ ⊢[PRAAx]
    embed (signedTerm A m t) ≐ GaussianScalarDeterminant.signedTerm (matrix A m m) m t :=
  (RationalGaussianEmbedding.embed_multiply _ _).eqTrans
    (qmul_congr (sign_embedding _ _) (product_matrix_embedding _ _ _))

theorem signed_body_at (A m t : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term signedBody t (pairT A m) ≐ signedTerm A m t := by
  simp only [RationalFiniteSum.term,signedBody,inst2,subst_signedTerm,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  ipra_congr (signedTerm (var 0) (var 1) (var 2) : PTm 3) with [fst_pair _ _, snd_pair _ _, .eqRefl t]

theorem determinant_embedding (A m : PTm n) : Γ ⊢[PRAAx]
    embed (determinant A m) ≐ GaussianScalarDeterminant.scalarDet (matrix A m m) m := by
  refine (RationalGaussianRealPart.embed_sum signedBody (count m) (pairT A m)).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ (count m) _ _ ?_).eqTrans
      (GaussianScalarDeterminant.scalar_leibniz _ _).eqSymm)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (count m)) :: Γ.map Fm.shift
  have lo := (embed_congr (signed_body_at (Γ := Δ) (Syn.shift A) (Syn.shift m) (var 0))).eqTrans
    (signed_term_embedding _ _ _)
  have hi := GaussianScalarDeterminant.signed_body_at (Γ := Δ)
    (matrix (Syn.shift A) (Syn.shift m) (Syn.shift m)) (Syn.shift m) (var 0)
  simpa only [Δ,Syn.shift,embedBody,inst2,RationalGaussianEmbedding.subst_embed,
    RationalFiniteSum.term,subst_pairT,RationalRowSpanGaussianEmbedding.subst_matrix] using lo.eqTrans hi.eqSymm

theorem determinant_well_formed (A m : PTm n) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (determinant A m) := RationalFiniteSum.sum_well_formed _ _ _
theorem determinant_axis (A m : PTm n) : Γ ⊢[PRAAx]
    RationalGaussianEmbedding.axis (GaussianScalarDeterminant.scalarDet (matrix A m m) m) :=
  RationalGaussianEmbedding.axis_congr (determinant_embedding A m) (RationalGaussianEmbedding.embed_axis _)
theorem determinant_real_part (A m : PTm n) : Γ ⊢[PRAAx]
    fstT (GaussianScalarDeterminant.scalarDet (matrix A m m) m) ≐ RationalArithmetic.recode (determinant A m) :=
  ((congrFst (determinant_embedding A m)).eqSymm.eqTrans (fst_pair _ _))

theorem determinant_zero_iff (A m : PTm n) : Γ ⊢[PRAAx] Fm.iff
    (RationalArgmin.rationalEq (determinant A m) scalarZero)
    (GaussianScalarDeterminant.scalarDet (matrix A m m) m ≐ qzero) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (determinant_embedding A m).eqSymm.eqTrans ((RationalGaussianEmbedding.zero_iff _).iffMpr Prf.hyp0)
  · exact (RationalGaussianEmbedding.zero_iff _).iffMp ((determinant_embedding A m).eqTrans Prf.hyp0)

theorem determinant_equality_iff (A B m k : PTm n) : Γ ⊢[PRAAx] Fm.iff
    (RationalArgmin.rationalEq (determinant A m) (determinant B k))
    (GaussianScalarDeterminant.scalarDet (matrix A m m) m ≐ GaussianScalarDeterminant.scalarDet (matrix B k k) k) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (determinant_embedding A m).eqSymm.eqTrans
      ((RationalGaussianEmbedding.embed_equal _ _ Prf.hyp0).eqTrans (determinant_embedding B k))
  · exact RationalGaussianEmbedding.rational_equal_of_embed _ _
      ((determinant_embedding A m).eqTrans (Prf.hyp0.eqTrans (determinant_embedding B k).eqSymm))

theorem empty_determinant (A : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalEq (determinant A zero) scalarOne :=
  RationalGaussianEmbedding.rational_equal_of_embed _ _ ((determinant_embedding A zero).eqTrans
    ((GaussianPolynomialDeterminant.empty_evaluation _ _ _).eqTrans RationalGaussianEmbedding.embed_one.eqSymm))

def determinantF : PR 2 := PTm.toPR (determinant (var 0) (var 1))
def output (A m : PTm n) : PTm n := pairT (determinant A m)
  (pairT (matrix A m m) (GaussianScalarDeterminant.run (matrix A m m) m))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (A m : PTm n) : PTm n := ap2 outputF A m
ipra_subst output
ipra_subst run
theorem determinant_at (A m : PTm n) : Γ ⊢[PRAAx] ap2 determinantF A m ≐ determinant A m := by
  simpa only [determinantF,ap2,subst_determinant,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (determinant (var 0) (var 1) : PTm 2) ![A,m]
theorem program_at (A m : PTm n) : Γ ⊢[PRAAx] run A m ≐ output A m := by
  simpa only [run,outputF,ap2,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![A,m]
theorem returned_rational (A m : PTm n) : Γ ⊢[PRAAx] fstT (run A m) ≐ determinant A m :=
  (program_at A m).fstE
theorem returned_matrix (A m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A m)) ≐ matrix A m m :=
  (program_at A m).sndE.fstE
theorem returned_gaussian_run (A m : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run A m)) ≐ GaussianScalarDeterminant.run (matrix A m m) m :=
  (program_at A m).sndE.sndE
theorem returned_gaussian_scalar (A m : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run A m)))) ≐ GaussianScalarDeterminant.scalarDet (matrix A m m) m :=
  (congrSnd (congrSnd (returned_gaussian_run A m))).eqTrans (GaussianScalarDeterminant.returned_scalar _ _)
theorem returned_embedding (A m : PTm n) : Γ ⊢[PRAAx]
    embed (fstT (run A m)) ≐ sndT (sndT (sndT (sndT (run A m)))) :=
  (embed_congr (returned_rational A m)).eqTrans ((determinant_embedding A m).eqTrans (returned_gaussian_scalar A m).eqSymm)

theorem actual_rational_product_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (product t (var 0) (var 1)) ≐ GaussianRationalFiniteProduct.qprod (embedBody t) (var 0) (var 1)) :=
  closeUniv 2 (product_embedding t _ _)
theorem actual_sign_branches_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((parity (var 0) (var 1) ≐ zero ⟶ sign (var 0) (var 1) ≐ scalarOne) ⋏
      (parity (var 0) (var 1) ≐ one ⟶ sign (var 0) (var 1) ≐ RationalArithmetic.negative scalarOne)) :=
  closeUniv 2 (.andI (.impI (sign_even _ _ Prf.hyp0)) (.impI (sign_odd _ _ Prf.hyp0)))
theorem actual_sign_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (sign (var 0) (var 1)) ≐ signPoint (var 0) (var 1)) := closeUniv 2 (sign_embedding _ _)
theorem actual_word_product_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (embed (rawProduct (var 0) (var 1) (var 2)) ≐
      GaussianScalarDeterminant.rawProduct (matrix (var 0) (var 1) (var 1)) (var 1) (var 2)) :=
  closeUniv 3 (product_matrix_embedding _ _ _)
theorem actual_signed_term_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (embed (signedTerm (var 0) (var 1) (var 2)) ≐
      GaussianScalarDeterminant.signedTerm (matrix (var 0) (var 1) (var 1)) (var 1) (var 2)) :=
  closeUniv 3 (signed_term_embedding _ _ _)
theorem actual_determinant_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (determinant (var 0) (var 1)) ≐ GaussianScalarDeterminant.scalarDet
      (matrix (var 0) (var 1) (var 1)) (var 1)) := closeUniv 2 (determinant_embedding _ _)
theorem actual_determinant_zero_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (RationalArgmin.rationalEq (determinant (var 0) (var 1)) scalarZero)
      (GaussianScalarDeterminant.scalarDet (matrix (var 0) (var 1) (var 1)) (var 1) ≐ qzero)) :=
  closeUniv 2 (determinant_zero_iff _ _)
theorem actual_determinant_axis_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (RationalGaussianEmbedding.axis (GaussianScalarDeterminant.scalarDet (matrix (var 0) (var 1) (var 1)) (var 1))) :=
  closeUniv 2 (determinant_axis _ _)
theorem actual_empty_determinant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (RationalArgmin.rationalEq (determinant (var 0) zero) scalarOne) := closeUniv 1 (empty_determinant _)
theorem actual_returned_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (embed (fstT (run (var 0) (var 1))) ≐ sndT (sndT (sndT (sndT (run (var 0) (var 1)))))) :=
  closeUniv 2 (returned_embedding _ _)

end LeanProofs.IPRA.Analysis.RationalScalarDeterminantGaussianEmbedding
