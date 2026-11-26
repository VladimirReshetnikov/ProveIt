import IPRADerivations.Analysis.Polynomials.GaussianPolynomialDeterminantTerms
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalConvolutionNorm
import IPRADerivations.Analysis.Polynomials.GaussianCoefficientNormOrder

/-!
# Norm of the actual determinant-word product

Each original table entry contributes a coefficient-norm factor bound.
Quantifier-free induction follows the original convolution stage and derives
its power bound. The numerical inversion sign preserves the bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantStageNorm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPolynomialDeterminantTerms
  (tableShape factor factor_length stage stage_zero stage_succ stage_length signPoint sign_even sign_odd term)
open GaussianCoefficientL1 (coefficientNorm prefixNorm prefix_succ)
open GaussianCoefficientNormOrder (coefficientNorm_congr coefficient_numerator_nonnegative)
open GaussianRationalMonicReduction (singleton singleton_length singleton_lookup)
open GaussianRationalL1 (qL1 qL1_guard)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalSyntheticBounds (natCode natCode_nonnegative natCode_multiply natCode_congr qL1_qone)
open GaussianRationalLinearProduct (norm_length scalar_zero_code scalar_zero_add scalar_multiply_one)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalArithmetic (multiply multiply_monotone)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def factorBounds (M m w R : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift m) ⟶
    rationalLE (coefficientNorm (factor (Syn.shift M) (Syn.shift m) (Syn.shift w) (var 0))) (natCode (Syn.shift R)))

@[simp] theorem subst_factorBounds {k : ℕ} (σ : Fin n → PTm k) (M m w R : PTm n) :
    (factorBounds M m w R).subst σ =
      factorBounds (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ R) := by
  simp [factorBounds, Syn.subst_shift, Syn.shift_subst]

theorem factor_at (M m w R j : PTm n) (h : Γ ⊢[PRAAx] factorBounds M m w R)
    (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (factor M m w j)) (natCode R) := by
  have at_j : Γ ⊢[PRAAx] lt j m ⟶ rationalLE (coefficientNorm (factor M m w j)) (natCode R) := by
    simpa only [Fm.subst_imp, subst_lt, RationalArgmin.subst_rationalLE,
      GaussianCoefficientL1.subst_coefficientNorm, GaussianPolynomialDeterminantTerms.subst_factor,
      GaussianRationalSyntheticBounds.subst_natCode, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h.allE j
  exact .impE at_j hj

theorem singleton_norm (q : PTm n) : Γ ⊢[PRAAx] coefficientNorm (singleton q) ≐ qL1 q := by
  have zero_sum := (GaussianCoefficientL1.prefix_zero (Γ := Γ) (singleton q)).eqTrans scalar_zero_code.eqSymm
  exact (norm_length _ _ (singleton_length q)).eqTrans ((prefix_succ _ zero).eqTrans
    ((RationalAlgebra.add_congr zero_sum (GaussianCoefficientL1.qL1_congr (singleton_lookup q))).eqTrans
      (scalar_zero_add _ (qL1_guard q))))

theorem sign_norm (m w : PTm n) : Γ ⊢[PRAAx] qL1 (signPoint m w) ≐ natCode one := by
  exact .orE (Foundations.RuntimePermutationWords.parity_cases m w)
    ((GaussianCoefficientL1.qL1_congr (sign_even m w Prf.hyp0)).eqTrans qL1_qone)
    ((GaussianCoefficientL1.qL1_congr (sign_odd m w Prf.hyp0)).eqTrans
      ((GaussianRationalL1Algebra.qL1_negative qone).eqTrans qL1_qone))

def normLaw (M m L w R j : PTm n) : Fm PTm n :=
  le j m ⟶ rationalLE (coefficientNorm (stage M m L w j)) (natCode (pw R j))

@[simp] theorem subst_normLaw {k : ℕ} (σ : Fin n → PTm k) (M m L w R j : PTm n) :
    (normLaw M m L w R j).subst σ =
      normLaw (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ R)
        (Syn.subst σ j) := by
  simp [normLaw, subst_ap2]

theorem norm_zero (M m L w R : PTm n) : Γ ⊢[PRAAx] normLaw M m L w R zero := by
  exact .impI (rationalLE_congr
    ((coefficientNorm_congr (stage_zero _ _ _ _)).eqTrans ((singleton_norm qone).eqTrans qL1_qone)).eqSymm
    (natCode_congr (pw_zero R)).eqSymm (reflexive _))

theorem norm_step (M m L w R j : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hf : Γ ⊢[PRAAx] factorBounds M m w R) (ih : Γ ⊢[PRAAx] normLaw M m L w R j) :
    Γ ⊢[PRAAx] normLaw M m L w R (succ j) := by
  refine .impI ?_
  have hj : le (succ j) m :: Γ ⊢[PRAAx] lt j m := Prf.hyp0
  have bounds := factor_at M m w R j hf.wk hj
  have previous := Prf.impE ih.wk (le_trans (le_succ_self j) hj)
  have product := GaussianRationalConvolutionNorm.product_norm (stage M m L w j) (factor M m w j)
    (j*L) L (stage_length _ _ _ _ _) (factor_length _ _ _ _ _ h.wk hj)
  have first := multiply_monotone (coefficientNorm (stage M m L w j)) _ _
    (coefficient_numerator_nonnegative _) bounds
  have swap := RationalAlgebra.multiply_commutative (Γ := le (succ j) m :: Γ)
    (coefficientNorm (stage M m L w j)) (natCode R)
  have second := multiply_monotone (natCode R) _ _ (natCode_nonnegative R) previous
  have rhs : le (succ j) m :: Γ ⊢[PRAAx] multiply (natCode R) (natCode (pw R j)) ≐ natCode (pw R (succ j)) :=
    (RationalAlgebra.multiply_commutative _ _).eqTrans ((natCode_multiply _ _).eqTrans (natCode_congr (pw_succ R j).eqSymm))
  exact rationalLE_congr (coefficientNorm_congr (stage_succ _ _ _ _ _)).eqSymm rhs
    (transitive product (transitive first (rationalLE_congr swap.eqSymm (.eqRefl _) second)))

theorem stage_norm (M m L w R j : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hf : Γ ⊢[PRAAx] factorBounds M m w R) (hj : Γ ⊢[PRAAx] le j m) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (stage M m L w j)) (natCode (pw R j)) := by
  have all : Γ ⊢[PRAAx] .all (normLaw (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift R) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [subst_normLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact norm_zero _ _ _ _ _
    · simp only [subst_normLaw, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hs : Γ.map Fm.shift ⊢[PRAAx] tableShape (Syn.shift M) (Syn.shift m) (Syn.shift L) := by
        simpa only [Fm.shift, Syn.shift, GaussianPolynomialDeterminantTerms.subst_tableShape] using h.shift
      have hfs : Γ.map Fm.shift ⊢[PRAAx] factorBounds (Syn.shift M) (Syn.shift m) (Syn.shift w) (Syn.shift R) := by
        simpa only [Fm.shift, Syn.shift, subst_factorBounds] using hf.shift
      exact norm_step _ _ _ _ _ _ hs.wk hfs.wk Prf.hyp0
  have rule : Γ ⊢[PRAAx] normLaw M m L w R j := by
    simpa only [subst_normLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem signed_term_norm (M m L w R : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hf : Γ ⊢[PRAAx] factorBounds M m w R) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (term M m L w)) (natCode (pw R m)) := by
  have scale := GaussianPolynomialNormBuffers.norm_scaled (Γ := Γ) (stage M m L w m) (signPoint m w)
  have eq := (RationalAlgebra.multiply_congr (sign_norm (Γ := Γ) m w) (.eqRefl (coefficientNorm (stage M m L w m)))).eqTrans
    ((RationalAlgebra.multiply_commutative _ _).eqTrans (scalar_multiply_one _ (GaussianCoefficientL1.norm_guard _)))
  exact transitive (rationalLE_congr (.eqRefl _) eq scale) (stage_norm _ _ _ _ _ _ h hf (le_refl m))

theorem actual_determinant_stage_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (tableShape (var 0) (var 1) (var 2) ⟶ factorBounds (var 0) (var 1) (var 3) (var 4) ⟶
      normLaw (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (stage_norm _ _ _ _ _ _ (Prf.wk Prf.hyp1) Prf.hyp1 Prf.hyp0))))

theorem actual_signed_determinant_term_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶ factorBounds (var 0) (var 1) (var 3) (var 4) ⟶
      rationalLE (coefficientNorm (term (var 0) (var 1) (var 2) (var 3))) (natCode (pw (var 4) (var 1)))) :=
  closeUniv 5 (.impI (.impI (signed_term_norm _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantStageNorm
