import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantNorm
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianPolynomialCoefficientDifferences

/-!
# Error summation for the actual runtime polynomial determinant

Matching signed summands are compared on the same actual retained word
scan. Their local coefficient-norm error bounds imply the error bound for
every computed determinant prefix and, using the proved retained-count
bound, the factorial error bound for the two actual determinants.
No matrix shape, product perturbation law or determinant error is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantError

open_ipra
open GaussianPolynomialDeterminant (summand partialDeterminant determinant width)
open GaussianCoefficientL1 (coefficientNorm subCoefficients)
open GaussianCoefficientNormOrder (coefficientNorm_congr subCoefficients_congr)
open GaussianRationalSyntheticBounds (natCode natCode_order add_monotone)
open GaussianPolynomialDeterminantNorm (natural_scale_zero natural_scale_succ)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalSupMetric (numeratorOf)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (count)
open LeanProofs.IPRA.Foundations.RuntimePermutationFactorialBound (factorial count_factorial_bound)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def termDifference (A B m L r : PTm n) : PTm n :=
  subCoefficients (summand A m L r) (summand B m L r) (width m L)
def difference (A B m L t : PTm n) : PTm n :=
  subCoefficients (partialDeterminant A m L t) (partialDeterminant B m L t) (width m L)
def summandBounds (A B m L K : PTm n) : Fm PTm n :=
  .all (lt (var 0) (count (Syn.shift m)) ⟶
    rationalLE (coefficientNorm (termDifference (Syn.shift A) (Syn.shift B) (Syn.shift m) (Syn.shift L) (var 0))) (Syn.shift K))
def prefixBound (A B m L K t : PTm n) : Fm PTm n :=
  le t (count m) ⟶ rationalLE (coefficientNorm (difference A B m L t)) (multiply (natCode t) K)

ipra_subst termDifference
ipra_subst difference
ipra_subst summandBounds [Syn.subst_shift, Syn.shift_subst]
ipra_subst prefixBound

theorem summand_bound_at (A B m L K r : PTm n) (h : Γ ⊢[PRAAx] summandBounds A B m L K)
    (hr : Γ ⊢[PRAAx] lt r (count m)) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (termDifference A B m L r)) K := by
  have query : Γ ⊢[PRAAx] lt r (count m) ⟶ rationalLE (coefficientNorm (termDifference A B m L r)) K := by
    simpa [summandBounds] using h.allE r
  exact .impE query hr

theorem budget_nonnegative (A B m L K : PTm n) (h : Γ ⊢[PRAAx] summandBounds A B m L K) :
    Γ ⊢[PRAAx] le (numeratorOf K).neg (numeratorOf K).pos :=
  GaussianRationalL1.nonnegative_of_lower _ _
    (GaussianCoefficientNormOrder.coefficient_numerator_nonnegative _)
    (summand_bound_at A B m L K zero h (Foundations.RuntimePermutationWords.words_nonempty m))

theorem difference_length (A B m L t : PTm n) :
    Γ ⊢[PRAAx] length (difference A B m L t) ≐ width m L :=
  GaussianCoefficientL1.zip_length GaussianCoefficientL1.subF _ _ _

theorem difference_zero_norm (A B m L : PTm n) :
    Γ ⊢[PRAAx] coefficientNorm (difference A B m L zero) ≐ natCode zero :=
  (coefficientNorm_congr (subCoefficients_congr (GaussianPolynomialDeterminant.prefix_zero A m L)
    (GaussianPolynomialDeterminant.prefix_zero B m L) (.eqRefl _))).eqTrans
      (GaussianCoefficientNormOrder.self_difference_norm _ _)

theorem difference_succ_bound (A B m L t : PTm n) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (difference A B m L (succ t)))
      (add (coefficientNorm (difference A B m L t)) (coefficientNorm (termDifference A B m L t))) :=
  rationalLE_congr (coefficientNorm_congr
    (subCoefficients_congr (GaussianPolynomialDeterminant.prefix_succ A m L t)
      (GaussianPolynomialDeterminant.prefix_succ B m L t) (.eqRefl _))).eqSymm (.eqRefl _)
    (GaussianPolynomialCoefficientDifferences.sum_difference_norm
      (partialDeterminant A m L t) (partialDeterminant B m L t) (summand A m L t) (summand B m L t) (width m L))

theorem prefix_error_bound (A B m L K t : PTm n) (h : Γ ⊢[PRAAx] summandBounds A B m L K)
    (ht : Γ ⊢[PRAAx] le t (count m)) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (difference A B m L t)) (multiply (natCode t) K) := by
  have all : Γ ⊢[PRAAx] .all (prefixBound (Syn.shift A) (Syn.shift B) (Syn.shift m) (Syn.shift L) (Syn.shift K) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_prefixBound]
    · refine .impI ?_
      exact rationalLE_congr (difference_zero_norm A B m L).eqSymm (natural_scale_zero K).eqSymm
        (RationalArgmin.reflexive (natCode zero))
    · refine .impI ?_
      let C := Syn.shift A
      let D := Syn.shift B
      let b := Syn.shift m
      let W := Syn.shift L
      let V := Syn.shift K
      let r : PTm (n+1) := var 0
      let Δ := le (succ r) (count b) :: prefixBound C D b W V r :: Γ.map Fm.shift
      have hr : Δ ⊢[PRAAx] lt r (count b) := Prf.hyp0
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] prefixBound C D b W V r) (le_of_lt hr)
      have shifted : Δ ⊢[PRAAx] summandBounds C D b W V := by
        simpa only [C,D,b,W,V,Δ,Fm.shift,subst_summandBounds,Syn.shift] using h.shift.wk.wk
      have estimate := RationalArgmin.transitive (difference_succ_bound (Γ := Δ) C D b W r)
        (add_monotone _ _ _ _ ih (summand_bound_at C D b W V r shifted hr))
      exact rationalLE_congr (.eqRefl _) (natural_scale_succ r V) estimate
  have guarded : Γ ⊢[PRAAx] prefixBound A B m L K t := by
    simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
  exact .impE guarded ht

theorem determinant_count_bound (A B m L K : PTm n) (h : Γ ⊢[PRAAx] summandBounds A B m L K) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (subCoefficients (determinant A m L) (determinant B m L) (width m L)))
      (multiply (natCode (count m)) K) :=
  prefix_error_bound A B m L K (count m) h (le_refl _)

theorem determinant_error_bound (A B m L K : PTm n) (h : Γ ⊢[PRAAx] summandBounds A B m L K) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (subCoefficients (determinant A m L) (determinant B m L) (width m L)))
      (multiply (natCode (factorial m)) K) := by
  have scale := RationalArithmetic.multiply_monotone K _ _ (budget_nonnegative A B m L K h)
    (natCode_order _ _ (count_factorial_bound m))
  have final := rationalLE_congr (RationalAlgebra.multiply_commutative _ _)
    (RationalAlgebra.multiply_commutative _ _) scale
  exact RationalArgmin.transitive (determinant_count_bound A B m L K h) final

def output (A B m L K t : PTm n) : PTm n := pairT (difference A B m L t)
  (pairT (coefficientNorm (difference A B m L t)) (multiply (natCode t) K))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (A B m L K t : PTm n) : PTm n := app outputF ![A,B,m,L,K,t]

ipra_subst output
ipra_subst run

theorem program_at (A B m L K t : PTm n) : Γ ⊢[PRAAx] run A B m L K t ≐ output A B m L K t := by
  simpa [run,outputF,app] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![A,B,m,L,K,t]

theorem returned_difference (A B m L K t : PTm n) :
    Γ ⊢[PRAAx] fstT (run A B m L K t) ≐ difference A B m L t :=
  (program_at A B m L K t).fstE
theorem returned_norm (A B m L K t : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run A B m L K t)) ≐ coefficientNorm (difference A B m L t) :=
  (program_at A B m L K t).sndE.fstE
theorem returned_budget (A B m L K t : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run A B m L K t)) ≐ multiply (natCode t) K :=
  (program_at A B m L K t).sndE.sndE
theorem returned_norm_is_actual (A B m L K t : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run A B m L K t)) ≐ coefficientNorm (fstT (run A B m L K t)) :=
  (returned_norm A B m L K t).eqTrans (coefficientNorm_congr (returned_difference A B m L K t)).eqSymm
theorem returned_length (A B m L K t : PTm n) : Γ ⊢[PRAAx]
    length (fstT (run A B m L K t)) ≐ width m L :=
  (congrFst (returned_difference A B m L K t)).eqTrans (difference_length A B m L t)

theorem returned_prefix_error_bound (A B m L K t : PTm n) (h : Γ ⊢[PRAAx] summandBounds A B m L K)
    (ht : Γ ⊢[PRAAx] le t (count m)) : Γ ⊢[PRAAx]
    rationalLE (fstT (sndT (run A B m L K t))) (sndT (sndT (run A B m L K t))) :=
  rationalLE_congr (returned_norm A B m L K t).eqSymm (returned_budget A B m L K t).eqSymm
    (prefix_error_bound A B m L K t h ht)

theorem returned_determinant_error_bound (A B m L K : PTm n) (h : Γ ⊢[PRAAx] summandBounds A B m L K) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (fstT (run A B m L K (count m)))) (multiply (natCode (factorial m)) K) :=
  rationalLE_congr (coefficientNorm_congr (returned_difference A B m L K (count m))).eqSymm (.eqRefl _)
    (determinant_error_bound A B m L K h)

theorem actual_zero_prefix_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coefficientNorm (difference (var 0) (var 1) (var 2) (var 3) zero) ≐ natCode zero) :=
  closeUniv 4 (difference_zero_norm _ _ _ _)
theorem actual_prefix_error_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (summandBounds (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le (var 5) (count (var 2)) ⟶
      rationalLE (coefficientNorm (difference (var 0) (var 1) (var 2) (var 3) (var 5)))
        (multiply (natCode (var 5)) (var 4))) :=
  closeUniv 6 (.impI (.impI (prefix_error_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_determinant_count_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (summandBounds (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      rationalLE (coefficientNorm (subCoefficients (determinant (var 0) (var 2) (var 3))
        (determinant (var 1) (var 2) (var 3)) (width (var 2) (var 3))))
        (multiply (natCode (count (var 2))) (var 4))) :=
  closeUniv 5 (.impI (determinant_count_bound _ _ _ _ _ Prf.hyp0))
theorem actual_determinant_factorial_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (summandBounds (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      rationalLE (coefficientNorm (subCoefficients (determinant (var 0) (var 2) (var 3))
        (determinant (var 1) (var 2) (var 3)) (width (var 2) (var 3))))
        (multiply (natCode (factorial (var 2))) (var 4))) :=
  closeUniv 5 (.impI (determinant_error_bound _ _ _ _ _ Prf.hyp0))
theorem actual_error_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_returned_error_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ≐
      coefficientNorm (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) :=
  closeUniv 6 (returned_norm_is_actual _ _ _ _ _ _)
theorem actual_returned_prefix_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (summandBounds (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le (var 5) (count (var 2)) ⟶
      rationalLE (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))
        (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))) :=
  closeUniv 6 (.impI (.impI (returned_prefix_error_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_determinant_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (summandBounds (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      rationalLE (coefficientNorm (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (count (var 2)))))
        (multiply (natCode (factorial (var 2))) (var 4))) :=
  closeUniv 5 (.impI (returned_determinant_error_bound _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantError
