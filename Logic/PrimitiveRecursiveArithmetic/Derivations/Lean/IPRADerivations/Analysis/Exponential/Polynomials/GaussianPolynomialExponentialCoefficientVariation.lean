import IPRADerivations.Analysis.Polynomials.Products.GaussianPolynomialPowerNormVariation
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponentialCoefficients
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianFiniteExponentialWeightedNorm

/-!
# Finite variation of the original polynomial exponential coefficients

The original coefficient-successor recurrence and actual power-prefix
norm estimate retain every original factorial weight. At any e<=N the
actual finite exponential coefficient changes by at most E times the
finite sum of j A^(j-1)/j!, j=1..K. The zero input constant is not
needed for this finite quantitative comparison. All original numerical
degrees, cutoffs, precision codes and rational error codes are internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialExponentialCoefficientVariation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (qsub)
open GaussianRationalL1 (qL1)
open GaussianCoefficientL1 (coefficientNorm subCoefficients qL1_congr)
open GaussianCoefficientNormOrder (coefficientNorm_congr)
open GaussianRationalSyntheticBounds (natCode add_monotone)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside exponent_outside)
open GaussianRationalPolynomialExponential (inverseFactorial)
open GaussianRationalPolynomialExponentialStability (coefficient exponent_congr)
open GaussianRationalPolynomialExponentialCoefficients (term)
open GaussianRationalPowerDifference (budget)
open GaussianRationalPolynomialPowers (prefix_length)
open RationalArithmetic (add multiply)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem exponent_error_norm (C D N e : PTm n) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (exponentCoefficient C N e) (exponentCoefficient D N e)))
      (coefficientNorm (subCoefficients C D (succ N))) := by
  refine .orE (lt_or_le N e) ?_ ?_
  · have eq := (qsub_congr (Γ := lt N e :: Γ) (exponent_outside C N e Prf.hyp0) (exponent_outside D N e Prf.hyp0)).eqTrans
      (GaussianCoefficientNormOrder.qsub_self qzero)
    exact RationalArgmin.rationalLE_congr ((qL1_congr eq).eqTrans GaussianRationalLinearProduct.qzero_norm).eqSymm
      (.eqRefl _) (GaussianCoefficientNormOrder.coefficient_nonnegative _)
  · have idx : (le e N :: Γ) ⊢[PRAAx] lt (LeanProofs.IPRA.PTm.monus N e) (succ N) :=
      (succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _)
    have codes := (qsub_congr (exponent_inside C N e Prf.hyp0) (exponent_inside D N e Prf.hyp0)).eqTrans
      (GaussianCoefficientL1.sub_lookup C D (succ N) _ idx).eqSymm
    exact RationalArgmin.rationalLE_congr (qL1_congr codes).eqSymm (.eqRefl _)
      (GaussianCoefficientNormEntries.coefficient_entry_bound _ _
        (lt_congr (.eqRefl _) (GaussianCoefficientL1.zip_length GaussianCoefficientL1.subF C D (succ N)).eqSymm idx))

def weight (A j : PTm n) : PTm n := multiply (qL1 (inverseFactorial (succ j))) (natCode (budget A one (succ j)))
def weightBody : PTm 2 := weight (var 1) (var 0)
def variationBudget (A j : PTm n) : PTm n := RationalFiniteSum.sum weightBody j A
@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (A j : PTm n) :
    Syn.subst σ (weight A j) = weight (Syn.subst σ A) (Syn.subst σ j) := by simp [weight]
@[simp] theorem subst_variationBudget {m : ℕ} (σ : Fin n → PTm m) (A j : PTm n) :
    Syn.subst σ (variationBudget A j) = variationBudget (Syn.subst σ A) (Syn.subst σ j) := by simp [variationBudget]

theorem weight_at (A j : PTm n) : RationalFiniteSum.term weightBody j A = weight A j := by
  simp [weightBody,RationalFiniteSum.term,inst2]
theorem weight_exact (A j : PTm n) : Γ ⊢[PRAAx] weight A j ≐
    GaussianEuclideanDistanceName.fraction (budget A one (succ j)) (Products.fact (succ j)) :=
  (RationalAlgebra.multiply_congr (GaussianFiniteExponentialWeightedNorm.inverse_factorial_norm (succ j)) (.eqRefl _)).eqTrans
    ((RationalNonnegativePowers.fraction_multiply one (Products.fact (succ j)) (budget A one (succ j)) one
      (GaussianRationalPolynomialExponential.factorial_positive _) (le_refl one)).eqTrans
        (RationalNonnegativePowers.fraction_congr (by ipra_ring) (by ipra_ring)))
theorem budget_zero (A : PTm n) : Γ ⊢[PRAAx] variationBudget A zero ≐ natCode zero :=
  (RationalFiniteSum.sum_zero weightBody A).eqTrans GaussianRationalLinearProduct.scalar_zero_code.eqSymm
theorem budget_succ (A j : PTm n) : Γ ⊢[PRAAx] variationBudget A (succ j) ≐ add (variationBudget A j) (weight A j) := by
  simpa only [variationBudget,weight_at] using RationalFiniteSum.sum_succ (Γ := Γ) weightBody j A

theorem budget_scale_succ (A E j : PTm n) : Γ ⊢[PRAAx]
    add (multiply (variationBudget A j) E) (multiply (weight A j) E) ≐ multiply (variationBudget A (succ j)) E :=
  (RationalAlgebra.add_congr (RationalAlgebra.multiply_commutative _ _) (RationalAlgebra.multiply_commutative _ _)).eqTrans
    ((RationalAlgebra.multiply_add E _ _).eqSymm.eqTrans
      ((RationalAlgebra.multiply_commutative _ _).eqTrans
        (RationalAlgebra.multiply_congr (budget_succ A j).eqSymm (.eqRefl E))))

theorem term_error (C D N K A E j e : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hA : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (natCode A))
    (hB : Γ ⊢[PRAAx] rationalLE (coefficientNorm D) (natCode A))
    (hE : Γ ⊢[PRAAx] rationalLE (coefficientNorm (subCoefficients C D (succ N))) E)
    (hj : Γ ⊢[PRAAx] le (succ j) K) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (term C N K e (succ j)) (term D N K e (succ j)))) (multiply (weight A j) E) := by
  have power := GaussianPolynomialPowerNormVariation.original_power_variation C D N K A E (succ j) hC hD hA hB hE hj
  have reader := RationalArgmin.transitive (exponent_error_norm _ _ _ e) power
  have scaled := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply _ _)
    (RationalArithmetic.multiply_monotone (qL1 (inverseFactorial (succ j))) _ _ (GaussianRationalL1.qL1_nonnegative _) reader)
  exact RationalArgmin.rationalLE_congr
    (qL1_congr (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _)).eqSymm
    (RationalAlgebra.multiply_associative _ _ _).eqSymm scaled

def errorLaw (C D N K A E e j : PTm n) : Fm PTm n := le j K ⟶
  rationalLE (qL1 (qsub (coefficient C N K j e) (coefficient D N K j e))) (multiply (variationBudget A j) E)
@[simp] theorem subst_errorLaw {m : ℕ} (σ : Fin n → PTm m) (C D N K A E e j : PTm n) :
    (errorLaw C D N K A E e j).subst σ = errorLaw (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ N)
      (Syn.subst σ K) (Syn.subst σ A) (Syn.subst σ E) (Syn.subst σ e) (Syn.subst σ j) := by simp [errorLaw]

theorem error_zero (C D N K A E e : PTm n) : Γ ⊢[PRAAx] errorLaw C D N K A E e zero := by
  refine .impI ?_
  have same := exponent_congr (Γ := le zero K :: Γ) ((GaussianRationalPolynomialExponential.stage_zero C N K).eqTrans
    (GaussianRationalPolynomialExponential.stage_zero D N K).eqSymm) (.eqRefl (zero*N)) (.eqRefl e)
  have lhs := (qL1_congr ((qsub_congr same (.eqRefl _)).eqTrans (GaussianCoefficientNormOrder.qsub_self _))).eqTrans
    GaussianRationalLinearProduct.qzero_norm
  have rhs := (RationalAlgebra.multiply_congr (budget_zero (Γ := le zero K :: Γ) A) (.eqRefl E)).eqTrans
    (GaussianPolynomialDeterminantNorm.natural_scale_zero E)
  exact RationalArgmin.rationalLE_congr lhs.eqSymm rhs.eqSymm (RationalArgmin.reflexive _)

theorem error_step (C D N K A E e j : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hA : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (natCode A))
    (hB : Γ ⊢[PRAAx] rationalLE (coefficientNorm D) (natCode A))
    (hE : Γ ⊢[PRAAx] rationalLE (coefficientNorm (subCoefficients C D (succ N))) E)
    (he : Γ ⊢[PRAAx] le e N) (ih : Γ ⊢[PRAAx] errorLaw C D N K A E e j) : Γ ⊢[PRAAx]
    errorLaw C D N K A E e (succ j) := by
  refine .impI ?_
  let Δ := le (succ j) K :: Γ
  have previous := Prf.impE ih.wk (le_trans (le_succ_self j) Prf.hyp0)
  have next := term_error C D N K A E j e hC.wk hD.wk hA.wk hB.wk hE.wk (Prf.hyp0 : Δ ⊢[PRAAx] le (succ j) K)
  have codes := (qsub_congr (Γ := Δ)
    (GaussianRationalPolynomialExponentialCoefficients.coefficient_recurrence C N K j e he.wk)
    (GaussianRationalPolynomialExponentialCoefficients.coefficient_recurrence D N K j e he.wk)).eqTrans
      (GaussianPolynomialCoefficientDifferences.scalar_sum_difference _ _ _ _)
  exact RationalArgmin.rationalLE_congr (qL1_congr codes).eqSymm (budget_scale_succ A E j)
    (RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_add _ _) (add_monotone _ _ _ _ previous next))

theorem original_coefficient_variation (C D N K A E e : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hA : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (natCode A))
    (hB : Γ ⊢[PRAAx] rationalLE (coefficientNorm D) (natCode A))
    (hE : Γ ⊢[PRAAx] rationalLE (coefficientNorm (subCoefficients C D (succ N))) E)
    (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub
      (exponentCoefficient (GaussianRationalPolynomialExponential.polynomial C N K) (K*N) e)
      (exponentCoefficient (GaussianRationalPolynomialExponential.polynomial D N K) (K*N) e)))
      (multiply (variationBudget A K) E) := by
  have all : Γ ⊢[PRAAx] .all (errorLaw (Syn.shift C) (Syn.shift D) (Syn.shift N) (Syn.shift K)
      (Syn.shift A) (Syn.shift E) (Syn.shift e) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact error_zero _ _ _ _ _ _ _
    · simp only [subst_errorLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      apply error_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0
      · simpa [Fm.shift,Syn.shift] using hC.shift.wk
      · simpa [Fm.shift,Syn.shift] using hD.shift.wk
      · simpa [Fm.shift,Syn.shift] using hA.shift.wk
      · simpa [Fm.shift,Syn.shift] using hB.shift.wk
      · simpa [Fm.shift,Syn.shift] using hE.shift.wk
      · simpa [Fm.shift,Syn.shift] using he.shift.wk
  have rule : Γ ⊢[PRAAx] errorLaw C D N K A E e K := by
    simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K
  exact Prf.impE rule (le_refl K)

theorem original_finite_exponential_coefficient_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 2) ⟶
      rationalLE (coefficientNorm (var 0)) (natCode (var 4)) ⟶ rationalLE (coefficientNorm (var 1)) (natCode (var 4)) ⟶
      rationalLE (coefficientNorm (subCoefficients (var 0) (var 1) (succ (var 2)))) (var 5) ⟶ le (var 6) (var 2) ⟶
      rationalLE (qL1 (qsub
        (exponentCoefficient (GaussianRationalPolynomialExponential.polynomial (var 0) (var 2) (var 3)) (var 3*var 2) (var 6))
        (exponentCoefficient (GaussianRationalPolynomialExponential.polynomial (var 1) (var 2) (var 3)) (var 3*var 2) (var 6))))
        (multiply (variationBudget (var 4) (var 3)) (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI
    (original_coefficient_variation _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))
theorem original_factorial_variation_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (weight (var 0) (var 1) ≐ GaussianEuclideanDistanceName.fraction
      (budget (var 0) one (succ (var 1))) (Products.fact (succ (var 1)))) :=
  closeUniv 2 (weight_exact _ _)

end LeanProofs.IPRA.Analysis.GaussianPolynomialExponentialCoefficientVariation
