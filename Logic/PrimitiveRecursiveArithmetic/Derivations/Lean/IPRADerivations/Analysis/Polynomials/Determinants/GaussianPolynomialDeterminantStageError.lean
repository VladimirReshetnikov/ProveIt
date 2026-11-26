import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantStageNorm
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialConvolutionDifference
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialCoefficientDifferences
import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantNorm

/-!
# Perturbing an actual determinant word

The two original convolution stages use the same word. A bound on each
pair of factor differences gives the exact prefix error budget
j * R^(j-1) * E, with zero error for the empty prefix. Both signed terms
use the same inversion sign.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantStageError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPolynomialDeterminantTerms
  (tableShape factor factor_length stage stage_zero stage_succ stage_length signPoint term)
open GaussianPolynomialDeterminantStageNorm (factorBounds factor_at stage_norm sign_norm)
open GaussianCoefficientL1 (coefficientNorm subCoefficients)
open GaussianCoefficientNormOrder
  (coefficientNorm_congr subCoefficients_congr coefficient_numerator_nonnegative self_difference_norm)
open GaussianRationalSyntheticBounds (natCode natCode_nonnegative natCode_add natCode_multiply natCode_congr add_monotone)
open GaussianRationalPowerDifference (budget budget_zero budget_step)
open GaussianPolynomialDeterminantNorm (natural_scale_zero)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalArithmetic (add multiply multiply_monotone)
open RationalAlgebra (add_congr multiply_congr multiply_add multiply_associative multiply_commutative)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def factorDifference (A B m L w j : PTm n) : PTm n :=
  subCoefficients (factor A m w j) (factor B m w j) (succ L)

def factorDifferences (A B m L w E : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift m) ⟶ rationalLE
    (coefficientNorm (factorDifference (Syn.shift A) (Syn.shift B) (Syn.shift m)
      (Syn.shift L) (Syn.shift w) (var 0))) (Syn.shift E))

def stageDifference (A B m L w j : PTm n) : PTm n :=
  subCoefficients (stage A m L w j) (stage B m L w j) (succ (j*L))

def errorLaw (A B m L w R E j : PTm n) : Fm PTm n :=
  le j m ⟶ rationalLE (coefficientNorm (stageDifference A B m L w j)) (multiply (natCode (budget R one j)) E)

@[simp] theorem subst_factorDifference {k : ℕ} (σ : Fin n → PTm k) (A B m L w j : PTm n) :
    Syn.subst σ (factorDifference A B m L w j) =
      factorDifference (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ m)
        (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ j) := by simp [factorDifference]

@[simp] theorem subst_factorDifferences {k : ℕ} (σ : Fin n → PTm k) (A B m L w E : PTm n) :
    (factorDifferences A B m L w E).subst σ =
      factorDifferences (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ m)
        (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ E) := by
  simp [factorDifferences, Syn.subst_shift, Syn.shift_subst]

@[simp] theorem subst_stageDifference {k : ℕ} (σ : Fin n → PTm k) (A B m L w j : PTm n) :
    Syn.subst σ (stageDifference A B m L w j) =
      stageDifference (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ m)
        (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ j) := by simp [stageDifference]

@[simp] theorem subst_errorLaw {k : ℕ} (σ : Fin n → PTm k) (A B m L w R E j : PTm n) :
    (errorLaw A B m L w R E j).subst σ = errorLaw (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ m)
      (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ j) := by simp [errorLaw]

theorem factor_difference_at (A B m L w E j : PTm n) (h : Γ ⊢[PRAAx] factorDifferences A B m L w E)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] rationalLE (coefficientNorm (factorDifference A B m L w j)) E := by
  have at_j : Γ ⊢[PRAAx] lt j m ⟶ rationalLE (coefficientNorm (factorDifference A B m L w j)) E := by
    simpa only [factorDifferences, Fm.subst_imp, subst_lt, RationalArgmin.subst_rationalLE,
      GaussianCoefficientL1.subst_coefficientNorm, subst_factorDifference, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h.allE j
  exact .impE at_j hj

/-- Scale the exact natural budget recurrence by the actual rational input. -/
theorem budget_succ_scale (R E j : PTm n) : Γ ⊢[PRAAx]
    add (multiply (multiply (natCode (budget R one j)) E) (natCode R))
        (multiply (natCode (pw R j)) E) ≐ multiply (natCode (budget R one (succ j))) E := by
  let K := natCode (budget R one j)
  let P := natCode (pw R j)
  let Q := natCode R
  have rotate : Γ ⊢[PRAAx] multiply (multiply K E) Q ≐ multiply E (multiply K Q) :=
    (multiply_congr (multiply_commutative K E) (.eqRefl Q)).eqTrans (multiply_associative E K Q)
  have sum := add_congr (Γ := Γ) rotate (multiply_commutative P E)
  have unit : Γ ⊢[PRAAx] pw R j ≐ pw R j * one :=
    ((mul_comm (pw R j) one).eqTrans (one_mul (pw R j))).eqSymm
  have natural : Γ ⊢[PRAAx] add (multiply K Q) P ≐ natCode (budget R one (succ j)) :=
    (add_congr (natCode_multiply _ _) (.eqRefl P)).eqTrans
      ((natCode_add _ _).eqTrans (natCode_congr
        ((congrAdd (.eqRefl _) unit).eqTrans (budget_step R one j))))
  exact sum.eqTrans ((multiply_add E (multiply K Q) P).eqSymm.eqTrans
    ((multiply_congr (.eqRefl E) natural).eqTrans (multiply_commutative _ _)))

theorem error_zero (A B m L w R E : PTm n) : Γ ⊢[PRAAx] errorLaw A B m L w R E zero := by
  refine .impI ?_
  have eq := subCoefficients_congr (Γ := le zero m :: Γ) (stage_zero A m L w) (stage_zero B m L w)
    (.eqRefl (succ (zero*L)))
  have lhs := (coefficientNorm_congr eq).eqTrans (self_difference_norm _ _)
  have rhs : le zero m :: Γ ⊢[PRAAx] multiply (natCode (budget R one zero)) E ≐ natCode zero :=
    (multiply_congr (natCode_congr (budget_zero R one)) (.eqRefl E)).eqTrans (natural_scale_zero E)
  exact rationalLE_congr lhs.eqSymm rhs.eqSymm (reflexive (natCode zero))

theorem error_step (A B m L w R E j : PTm n)
    (ha : Γ ⊢[PRAAx] tableShape A m L) (hb : Γ ⊢[PRAAx] tableShape B m L)
    (hfa : Γ ⊢[PRAAx] factorBounds A m w R) (hfb : Γ ⊢[PRAAx] factorBounds B m w R)
    (hf : Γ ⊢[PRAAx] factorDifferences A B m L w E)
    (ih : Γ ⊢[PRAAx] errorLaw A B m L w R E j) :
    Γ ⊢[PRAAx] errorLaw A B m L w R E (succ j) := by
  refine .impI ?_
  let Δ := le (succ j) m :: Γ
  have hJ : Δ ⊢[PRAAx] lt j m := Prf.hyp0
  have hJ' : Δ ⊢[PRAAx] le j m := le_of_lt hJ
  have hd := factor_difference_at A B m L w E j hf.wk hJ
  have he := GaussianRationalL1.nonnegative_of_lower _ _ (coefficient_numerator_nonnegative _) hd
  have prior := Prf.impE ih.wk hJ'
  have hA := factor_at A m w R j hfa.wk hJ
  have hB := stage_norm B m L w R j hb.wk hfb.wk hJ'
  have firstBound := multiply_monotone (coefficientNorm (stageDifference A B m L w j)) _ _
    (coefficient_numerator_nonnegative _) hA
  have firstBudget := multiply_monotone (natCode R) _ _ (natCode_nonnegative _) prior
  have first := transitive firstBound (rationalLE_congr (multiply_commutative _ _)
    (multiply_commutative _ _) firstBudget)
  have secondBound := multiply_monotone (coefficientNorm (stage B m L w j)) _ _
    (coefficient_numerator_nonnegative _) hd
  have secondBudget := multiply_monotone E _ _ he hB
  have second := transitive secondBound (rationalLE_congr (multiply_commutative _ _)
    (multiply_commutative _ _) secondBudget)
  have stepInput : Δ ⊢[PRAAx] GaussianPolynomialConvolutionDifference.input
      (stage A m L w j) (factor A m w j) (stage B m L w j) (factor B m w j) (j*L) L :=
    .andI (stage_length _ _ _ _ _) (.andI (factor_length _ _ _ _ _ ha.wk hJ)
      (.andI (stage_length _ _ _ _ _) (factor_length _ _ _ _ _ hb.wk hJ)))
  have step := GaussianPolynomialConvolutionDifference.error_norm_bound _ _ _ _ _ _ stepInput
  have lhs : Δ ⊢[PRAAx] stageDifference A B m L w (succ j) ≐
      GaussianPolynomialConvolutionDifference.difference
        (stage A m L w j) (factor A m w j) (stage B m L w j) (factor B m w j) (j*L) L :=
    subCoefficients_congr (stage_succ _ _ _ _ _) (stage_succ _ _ _ _ _) (congrSucc (succ_mul j L))
  exact rationalLE_congr (coefficientNorm_congr lhs).eqSymm (budget_succ_scale R E j)
    (transitive step (add_monotone _ _ _ _ first second))

theorem stage_error (A B m L w R E j : PTm n)
    (ha : Γ ⊢[PRAAx] tableShape A m L) (hb : Γ ⊢[PRAAx] tableShape B m L)
    (hfa : Γ ⊢[PRAAx] factorBounds A m w R) (hfb : Γ ⊢[PRAAx] factorBounds B m w R)
    (hf : Γ ⊢[PRAAx] factorDifferences A B m L w E) (hj : Γ ⊢[PRAAx] le j m) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (stageDifference A B m L w j)) (multiply (natCode (budget R one j)) E) := by
  have all : Γ ⊢[PRAAx] .all (errorLaw (Syn.shift A) (Syn.shift B) (Syn.shift m) (Syn.shift L)
      (Syn.shift w) (Syn.shift R) (Syn.shift E) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [subst_errorLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact error_zero _ _ _ _ _ _ _
    · simp only [subst_errorLaw, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      apply error_step _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0
      · simpa only [Fm.shift, Syn.shift, GaussianPolynomialDeterminantTerms.subst_tableShape] using ha.shift.wk
      · simpa only [Fm.shift, Syn.shift, GaussianPolynomialDeterminantTerms.subst_tableShape] using hb.shift.wk
      · simpa only [Fm.shift, Syn.shift, GaussianPolynomialDeterminantStageNorm.subst_factorBounds] using hfa.shift.wk
      · simpa only [Fm.shift, Syn.shift, GaussianPolynomialDeterminantStageNorm.subst_factorBounds] using hfb.shift.wk
      · simpa only [Fm.shift, Syn.shift, subst_factorDifferences] using hf.shift.wk
  have rule : Γ ⊢[PRAAx] errorLaw A B m L w R E j := by
    simpa only [subst_errorLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem signed_term_error (A B m L w R E : PTm n)
    (ha : Γ ⊢[PRAAx] tableShape A m L) (hb : Γ ⊢[PRAAx] tableShape B m L)
    (hfa : Γ ⊢[PRAAx] factorBounds A m w R) (hfb : Γ ⊢[PRAAx] factorBounds B m w R)
    (hf : Γ ⊢[PRAAx] factorDifferences A B m L w E) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (subCoefficients (term A m L w) (term B m L w) (succ (m*L))))
      (multiply (natCode (budget R one m)) E) := by
  have scale := GaussianPolynomialCoefficientDifferences.scaled_difference_norm
    (stage A m L w m) (stage B m L w m) (succ (m*L)) (signPoint m w)
    (stage_length (Γ := Γ) _ _ _ _ _) (stage_length _ _ _ _ _)
  have eq := (multiply_congr (sign_norm (Γ := Γ) m w) (.eqRefl (coefficientNorm (stageDifference A B m L w m)))).eqTrans
    ((multiply_commutative _ _).eqTrans (GaussianRationalLinearProduct.scalar_multiply_one _ (GaussianCoefficientL1.norm_guard _)))
  exact transitive (rationalLE_congr (.eqRefl _) eq scale) (stage_error _ _ _ _ _ _ _ _ ha hb hfa hfb hf (le_refl m))

def pairInput (A B m L w R E : PTm n) : Fm PTm n :=
  (tableShape A m L ⋏ tableShape B m L) ⋏
    ((factorBounds A m w R ⋏ factorBounds B m w R) ⋏ factorDifferences A B m L w E)

theorem actual_stage_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (pairInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      errorLaw (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) := by
  refine closeUniv 8 (.impI (.impI ?_))
  let H := pairInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (n := 8)
  have h : le (var 7) (var 2) :: [H] ⊢[PRAAx] H := Prf.hyp1
  have shapes := Prf.andE₁ h
  have factors := Prf.andE₁ (Prf.andE₂ h)
  exact stage_error _ _ _ _ _ _ _ _ (.andE₁ shapes) (.andE₂ shapes)
    (.andE₁ factors) (.andE₂ factors) (.andE₂ (.andE₂ h)) Prf.hyp0

theorem actual_signed_term_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (pairInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      rationalLE (coefficientNorm (subCoefficients (term (var 0) (var 2) (var 3) (var 4))
        (term (var 1) (var 2) (var 3) (var 4)) (succ (var 2*var 3))))
        (multiply (natCode (budget (var 5) one (var 2))) (var 6))) := by
  refine closeUniv 7 (.impI ?_)
  let H := pairInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (n := 7)
  have h : [H] ⊢[PRAAx] H := Prf.hyp0
  have shapes := Prf.andE₁ h
  have factors := Prf.andE₁ (Prf.andE₂ h)
  exact signed_term_error _ _ _ _ _ _ _ (.andE₁ shapes) (.andE₂ shapes)
    (.andE₁ factors) (.andE₂ factors) (.andE₂ (.andE₂ h))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantStageError
