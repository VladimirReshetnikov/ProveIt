import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminant
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianPolynomialNormBuffers
import IPRADerivations.Foundations.RuntimePermutationFactorialBound
import IPRADerivations.Core.LinearCombination

/-!
# Norm bounds for the actual runtime polynomial determinant

Bounds on the actual retained signed summands give a bound for every
computed determinant prefix. The retained count is bounded by the actual
factorial, so the same summand budget gives the factorial determinant
bound. Quantifier-free induction follows the original prefix program;
no product-stage norm formula or supplied prefix bound is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantNorm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPolynomialDeterminant (summand partialDeterminant determinant width)
open GaussianCoefficientL1 (coefficientNorm)
open GaussianCoefficientNormOrder (coefficientNorm_congr coefficient_nonnegative)
open GaussianRationalSyntheticBounds (natCode natCode_represents natCode_order add_monotone)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (count)
open LeanProofs.IPRA.Foundations.RuntimePermutationFactorialBound (factorial count_factorial_bound)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def summandBounds (M m L K : PTm n) : Fm PTm n :=
  .all (lt (var 0) (count (Syn.shift m)) ⟶
    rationalLE (coefficientNorm (summand (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0))) (Syn.shift K))

def prefixBound (M m L K t : PTm n) : Fm PTm n :=
  le t (count m) ⟶ rationalLE (coefficientNorm (partialDeterminant M m L t)) (multiply (natCode t) K)

@[simp] theorem subst_summandBounds {l : ℕ} (σ : Fin n → PTm l) (M m L K : PTm n) :
    (summandBounds M m L K).subst σ = summandBounds (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ K) := by
  simp [summandBounds,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_prefixBound {l : ℕ} (σ : Fin n → PTm l) (M m L K t : PTm n) :
    (prefixBound M m L K t).subst σ = prefixBound (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ K) (Syn.subst σ t) := by
  simp [prefixBound]

theorem summand_bound_at (M m L K r : PTm n) (h : Γ ⊢[PRAAx] summandBounds M m L K)
    (hr : Γ ⊢[PRAAx] lt r (count m)) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (summand M m L r)) K := by
  have query : Γ ⊢[PRAAx] lt r (count m) ⟶ rationalLE (coefficientNorm (summand M m L r)) K := by
    simpa [summandBounds] using h.allE r
  exact .impE query hr

theorem budget_nonnegative (M m L K : PTm n) (h : Γ ⊢[PRAAx] summandBounds M m L K) :
    Γ ⊢[PRAAx] le (numeratorOf K).neg (numeratorOf K).pos :=
  GaussianRationalL1.nonnegative_of_lower _ _
    (GaussianCoefficientNormOrder.coefficient_numerator_nonnegative _)
    (summand_bound_at M m L K zero h (Foundations.RuntimePermutationWords.words_nonempty m))

/-- Natural scaling identities hold for arbitrary raw rational budgets. -/
theorem natural_scale_zero (K : PTm n) : Γ ⊢[PRAAx] multiply (natCode zero) K ≐ natCode zero := by
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) (natCode zero) K _ _ _ _
    (natCode_represents zero) (RationalRepresentations.represents_self K)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) rep (natCode_represents zero)
    (RationalAlgebra.positive_product (le_refl one) (RationalArgmin.denominator_positive K)) (le_refl one)
  ipra_lc

theorem natural_scale_succ (t K : PTm n) : Γ ⊢[PRAAx]
    add (multiply (natCode t) K) K ≐ multiply (natCode (succ t)) K := by
  have p := RationalRepresentations.represents_multiply (Γ := Γ) (natCode t) K _ _ _ _
    (natCode_represents t) (RationalRepresentations.represents_self K)
  have left := RationalRepresentations.represents_add (Γ := Γ) (multiply (natCode t) K) K _ _ _ _
    p (RationalRepresentations.represents_self K)
  have right := RationalRepresentations.represents_multiply (Γ := Γ) (natCode (succ t)) K _ _ _ _
    (natCode_represents (succ t)) (RationalRepresentations.represents_self K)
  have hd := RationalArgmin.denominator_positive (Γ := Γ) K
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalArithmetic.multiply_guard _ _) left right
    (RationalAlgebra.positive_product (RationalAlgebra.positive_product (le_refl one) hd) hd)
    (RationalAlgebra.positive_product (le_refl one) hd)
  ipra_lc

theorem prefix_norm_bound (M m L K t : PTm n) (h : Γ ⊢[PRAAx] summandBounds M m L K)
    (ht : Γ ⊢[PRAAx] le t (count m)) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (partialDeterminant M m L t)) (multiply (natCode t) K) := by
  have all : Γ ⊢[PRAAx] .all (prefixBound (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift K) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI ?_
      exact rationalLE_congr
        ((coefficientNorm_congr (GaussianPolynomialDeterminant.prefix_zero M m L)).eqTrans
          (GaussianPolynomialNormBuffers.norm_zeros _)).eqSymm
        (natural_scale_zero K).eqSymm (RationalArgmin.reflexive (natCode zero))
    · simp only [subst_prefixBound,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let A := Syn.shift M
      let b := Syn.shift m
      let B := Syn.shift L
      let V := Syn.shift K
      let r : PTm (n+1) := var 0
      let Δ := le (succ r) (count b) :: prefixBound A b B V r :: Γ.map Fm.shift
      have hr : Δ ⊢[PRAAx] lt r (count b) := Prf.hyp0
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] prefixBound A b B V r) (le_of_lt hr)
      have shifted : Δ ⊢[PRAAx] summandBounds A b B V := by
        simpa only [A,b,B,V,Δ,Fm.shift,subst_summandBounds,Syn.shift] using h.shift.wk.wk
      have termBound := summand_bound_at A b B V r shifted hr
      have triangle := GaussianPolynomialNormBuffers.norm_added
        (Γ := Δ) (partialDeterminant A b B r) (summand A b B r) (width b B)
        (GaussianPolynomialDeterminant.prefix_length A b B r)
        (GaussianPolynomialDeterminantTerms.term_length A b B (GaussianPolynomialDeterminant.wordCode b r))
      have estimate := RationalArgmin.transitive triangle (add_monotone _ _ _ _ ih termBound)
      exact rationalLE_congr (coefficientNorm_congr (GaussianPolynomialDeterminant.prefix_succ A b B r)).eqSymm
        (natural_scale_succ r V) estimate
  have guarded : Γ ⊢[PRAAx] prefixBound M m L K t := by
    simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
  exact .impE guarded ht

theorem determinant_count_bound (M m L K : PTm n) (h : Γ ⊢[PRAAx] summandBounds M m L K) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (determinant M m L)) (multiply (natCode (count m)) K) :=
  prefix_norm_bound M m L K (count m) h (le_refl _)

theorem determinant_norm_bound (M m L K : PTm n) (h : Γ ⊢[PRAAx] summandBounds M m L K) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (determinant M m L)) (multiply (natCode (factorial m)) K) := by
  have scale := RationalArithmetic.multiply_monotone K _ _ (budget_nonnegative M m L K h)
    (natCode_order _ _ (count_factorial_bound m))
  have final := rationalLE_congr (RationalAlgebra.multiply_commutative _ _)
    (RationalAlgebra.multiply_commutative _ _) scale
  exact RationalArgmin.transitive (determinant_count_bound M m L K h) final

/-! The returned polynomial is the existing prefix program, accompanied
by its actual computed norm and the numerical prefix budget. -/

def output (M m L K t : PTm n) : PTm n := pairT (partialDeterminant M m L t)
  (pairT (coefficientNorm (partialDeterminant M m L t)) (multiply (natCode t) K))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (M m L K t : PTm n) : PTm n := app outputF ![M,m,L,K,t]

@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (M m L K t : PTm n) :
    Syn.subst σ (output M m L K t) = output (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ K) (Syn.subst σ t) := by
  simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (M m L K t : PTm n) :
    Syn.subst σ (run M m L K t) = run (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ K) (Syn.subst σ t) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (M m L K t : PTm n) : Γ ⊢[PRAAx] run M m L K t ≐ output M m L K t := by
  simpa [run,outputF,app] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![M,m,L,K,t]

theorem returned_prefix (M m L K t : PTm n) :
    Γ ⊢[PRAAx] fstT (run M m L K t) ≐ partialDeterminant M m L t :=
  (congrFst (program_at M m L K t)).eqTrans (fst_pair _ _)
theorem returned_norm (M m L K t : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run M m L K t)) ≐ coefficientNorm (partialDeterminant M m L t) :=
  (congrFst ((congrSnd (program_at M m L K t)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_budget (M m L K t : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run M m L K t)) ≐ multiply (natCode t) K :=
  (congrSnd ((congrSnd (program_at M m L K t)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_norm_is_actual (M m L K t : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run M m L K t)) ≐ coefficientNorm (fstT (run M m L K t)) :=
  (returned_norm M m L K t).eqTrans (coefficientNorm_congr (returned_prefix M m L K t)).eqSymm

theorem returned_prefix_bound (M m L K t : PTm n) (h : Γ ⊢[PRAAx] summandBounds M m L K)
    (ht : Γ ⊢[PRAAx] le t (count m)) : Γ ⊢[PRAAx]
    rationalLE (fstT (sndT (run M m L K t))) (sndT (sndT (run M m L K t))) :=
  rationalLE_congr (returned_norm M m L K t).eqSymm (returned_budget M m L K t).eqSymm
    (prefix_norm_bound M m L K t h ht)

theorem returned_determinant (M m L K : PTm n) :
    Γ ⊢[PRAAx] fstT (run M m L K (count m)) ≐ determinant M m L :=
  returned_prefix M m L K (count m)
theorem returned_determinant_bound (M m L K : PTm n) (h : Γ ⊢[PRAAx] summandBounds M m L K) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (fstT (run M m L K (count m)))) (multiply (natCode (factorial m)) K) :=
  rationalLE_congr (coefficientNorm_congr (returned_determinant M m L K)).eqSymm (.eqRefl _)
    (determinant_norm_bound M m L K h)

theorem actual_prefix_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (summandBounds (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (count (var 1)) ⟶
      rationalLE (coefficientNorm (partialDeterminant (var 0) (var 1) (var 2) (var 4)))
        (multiply (natCode (var 4)) (var 3))) :=
  closeUniv 5 (.impI (.impI (prefix_norm_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_determinant_count_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (summandBounds (var 0) (var 1) (var 2) (var 3) ⟶
      rationalLE (coefficientNorm (determinant (var 0) (var 1) (var 2)))
        (multiply (natCode (count (var 1))) (var 3))) :=
  closeUniv 4 (.impI (determinant_count_bound _ _ _ _ Prf.hyp0))
theorem actual_determinant_factorial_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (summandBounds (var 0) (var 1) (var 2) (var 3) ⟶
      rationalLE (coefficientNorm (determinant (var 0) (var 1) (var 2)))
        (multiply (natCode (factorial (var 1))) (var 3))) :=
  closeUniv 4 (.impI (determinant_norm_bound _ _ _ _ Prf.hyp0))
theorem actual_norm_prefix_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐
      coefficientNorm (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (returned_norm_is_actual _ _ _ _ _)
theorem actual_returned_prefix_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (summandBounds (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (count (var 1)) ⟶
      rationalLE (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))
        (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.impI (.impI (returned_prefix_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_determinant_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (summandBounds (var 0) (var 1) (var 2) (var 3) ⟶
      rationalLE (coefficientNorm (fstT (run (var 0) (var 1) (var 2) (var 3) (count (var 1)))))
        (multiply (natCode (factorial (var 1))) (var 3))) :=
  closeUniv 4 (.impI (returned_determinant_bound _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantNorm
