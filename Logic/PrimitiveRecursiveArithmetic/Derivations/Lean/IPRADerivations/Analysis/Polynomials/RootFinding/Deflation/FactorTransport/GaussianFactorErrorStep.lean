import IPRADerivations.Analysis.Polynomials.RootFinding.Deflation.GaussianRationalDeflationError
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalReconstruction
import IPRADerivations.Analysis.Polynomials.RootFinding.Deflation.FactorTransport.GaussianFactorBounds
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNormOrder

/-!
# Actual local errors in finite rational approximate factorization

The target at stage j is the actual suffix product reconstructed from the
final root list of the actual deflation run. Its coefficient error is an
actual finite normalized coefficient difference and norm sum. The terminal
zero and the local error recurrence are derived from the true synthetic
quotient, true root lookup, proved residuals and proved root radii. The only
existence premise is the stated monic local RD contract.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFactorErrorStep

open_ipra
open LeanProofs.IPRA.Analysis.GaussianFactorParameters
  (initialA toleranceDenominator polynomial rootAt roots monicRD)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Analysis.GaussianRationalDeflation (remaining subst_remaining singleton)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds (natCode natCode_add natCode_congr add_monotone)
open LeanProofs.IPRA.Analysis.GaussianCoefficientL1 (coefficientNorm subCoefficients)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNormOrder
  (coefficientNorm_congr subCoefficients_congr coefficient_numerator_nonnegative)
open LeanProofs.IPRA.Analysis.GaussianRationalDeflationError (inputError quotientError)
open LeanProofs.IPRA.Analysis.GaussianRationalReconstruction (suffix)
open LeanProofs.IPRA.Analysis.RationalArithmetic (add multiply)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def target (step : PR 3) (C N p q j : PTm n) : PTm n := suffix (roots step C N p q N) N j
def errorCoefficients (step : PR 3) (C N p q j : PTm n) : PTm n :=
  subCoefficients (polynomial step C N p q j) (target step C N p q j) (succ (remaining N j))
def error (step : PR 3) (C N p q j : PTm n) : PTm n :=
  coefficientNorm (errorCoefficients step C N p q j)
def fraction (a F : PTm n) : PTm n := normalize (ZT.ofNat a) F

ipra_subst target
ipra_subst errorCoefficients
ipra_subst error
ipra_subst fraction

/-- Canonical scalar storage is a consequence of the actual norm producer. -/
theorem error_guard (step : PR 3) (C N p q j : PTm n) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (error step C N p q j) := GaussianCoefficientL1.norm_guard _

theorem error_congr (step : PR 3) {C C' N N' p p' q q' i j : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ C') (hN : Γ ⊢[PRAAx] N ≐ N')
    (hp : Γ ⊢[PRAAx] p ≐ p') (hq : Γ ⊢[PRAAx] q ≐ q') (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx]
    error step C N p q i ≐ error step C' N' p' q' j := by
  ipra_congr (error step (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hC, hN, hp, hq, hi]

theorem error_index_congr (step : PR 3) (C N p q : PTm n) {i j : PTm n}
    (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx] error step C N p q i ≐ error step C N p q j :=
  error_congr step (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) hi

theorem error_initial (step : PR 3) (C N p q : PTm n) : Γ ⊢[PRAAx]
    error step C N p q zero ≐ coefficientNorm (subCoefficients C
      (GaussianRationalReconstruction.reconstruct (roots step C N p q N) N N) (succ N)) :=
  coefficientNorm_congr (subCoefficients_congr
    (GaussianRationalDeflation.polynomial_zero step C N p (toleranceDenominator C N q))
    (GaussianRationalReconstruction.suffix_zero (roots step C N p q N) N)
    (congrSucc (monus_zero N)))

theorem target_step (step : PR 3) (C N p q j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    target step C N p q j ≐ GaussianRationalLinearProduct.linear
      (target step C N p q (succ j)) (rootAt step C N p q j) (remaining N j) :=
  (GaussianRationalReconstruction.suffix_step (roots step C N p q N) N j hj).eqTrans
    (GaussianRationalReconstruction.linear_congr (.eqRefl _)
      (GaussianRationalDeflation.roots_lookup step C N p (toleranceDenominator C N q) N j hj) (.eqRefl _))

theorem error_input (step : PR 3) (C N p q j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    error step C N p q j ≐ coefficientNorm (inputError (polynomial step C N p q j)
      (target step C N p q (succ j)) (rootAt step C N p q j) (remaining N j)) :=
  coefficientNorm_congr (subCoefficients_congr (.eqRefl _) (target_step step C N p q j hj) (.eqRefl _))

theorem error_quotient (step : PR 3) (C N p q j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    coefficientNorm (quotientError (polynomial step C N p q j) (target step C N p q (succ j))
      (rootAt step C N p q j) (remaining N j)) ≐ error step C N p q (succ j) :=
  coefficientNorm_congr (subCoefficients_congr
    (GaussianRationalDeflation.polynomial_succ step C N p (toleranceDenominator C N q) j).eqSymm
    (.eqRefl _) (GaussianRationalDeflation.remaining_step N j hj))

theorem error_nonnegative (step : PR 3) (C N p q j : PTm n) : Γ ⊢[PRAAx]
    rationalLE (natCode zero) (error step C N p q j) :=
  GaussianCoefficientNormOrder.coefficient_nonnegative _

theorem error_numerator_nonnegative (step : PR 3) (C N p q j : PTm n) : Γ ⊢[PRAAx]
    le (RationalSupMetric.numeratorOf (error step C N p q j)).neg
      (RationalSupMetric.numeratorOf (error step C N p q j)).pos := coefficient_numerator_nonnegative _

/-- The true last quotient and true empty suffix are both literally one.
The normalized self-difference therefore has actual scalar zero norm. -/
theorem final_error_zero (step : PR 3) (C N p q : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] error step C N p q N ≐ natCode zero :=
  (coefficientNorm_congr (subCoefficients_congr
    (GaussianRationalDeflation.final_polynomial_one step C N p (toleranceDenominator C N q) hC hm hN)
    (GaussianRationalReconstruction.suffix_final (roots step C N p q N) N)
    (congrSucc (monus_self N)))).eqTrans
      (GaussianCoefficientNormOrder.self_difference_norm (singleton qone) (succ zero))

/-- The source Euclidean residual estimate supplies exactly the allowed
factor two for the actual coefficient L1 residual. -/
theorem residual_l1_bound (step : PR 3) (C N p q j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (evaluate (polynomial step C N p q j) (rootAt step C N p q j)))
      (fraction (two*p) (toleranceDenominator C N q)) :=
  GaussianRationalL1Algebra.qL1_of_bounded _ _ _
    (GaussianFactorParameters.tolerance_positive C N q hN (le_trans hp hpq))
    (GaussianFactorParameters.stage_residual step C N p q j hRD hC hm hN hp (le_trans hp hpq) hj)

/-- The proved radius of the actual stage root gives the exact source
linear-factor coefficient-norm multiplier 2 A_j + 5. -/
theorem root_factor_bound (step : PR 3) (C N p q j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    rationalLE (add (natCode one) (qL1 (rootAt step C N p q j)))
      (natCode (GaussianFactorBudget.factor N (initialA C) j)) := by
  have radius := GaussianFactorBounds.all_root_radii step C N p q j hRD hC hm hN hp hpq hj
  have l1 := GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (le_refl one) radius
  have sum := add_monotone _ _ _ _ (RationalArgmin.reflexive (natCode one)) l1
  have integer : Γ ⊢[PRAAx] add (natCode one) (natCode (two*(GaussianFactorBounds.stageBound C N j+two))) ≐
      natCode (GaussianFactorBudget.factor N (initialA C) j) :=
    (natCode_add _ _).eqTrans (natCode_congr (by unfold GaussianFactorBudget.factor GaussianFactorBounds.stageBound GaussianFactorBudget.five; ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) integer sum

/-- Actual error transport for every active numerical stage. No error,
radius, residual, quotient or factorization recurrence is an input. -/
theorem error_step (step : PR 3) (C N p q j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    rationalLE (error step C N p q j)
      (add (fraction (two*p) (toleranceDenominator C N q))
        (multiply (natCode (GaussianFactorBudget.factor N (initialA C) j)) (error step C N p q (succ j)))) := by
  have shape := GaussianFactorBounds.stage_shape step C N p q j hC hm (le_trans (le_succ_self _) hj)
  have actualBound := GaussianRationalDeflationError.deflation_error_bound (polynomial step C N p q j)
    (target step C N p q (succ j)) (rootAt step C N p q j) (remaining N j) (Prf.andE₁ shape)
  have errorBound := RationalArgmin.rationalLE_congr (error_input step C N p q j hj).eqSymm
    (RationalAlgebra.add_congr (.eqRefl _)
      (RationalAlgebra.multiply_congr (.eqRefl _) (error_quotient step C N p q j hj))) actualBound
  have multiplier := RationalArithmetic.multiply_monotone (error step C N p q (succ j)) _ _
    (error_numerator_nonnegative step C N p q (succ j)) (root_factor_bound step C N p q j hRD hC hm hN hp hpq hj)
  have multiplier' := RationalArgmin.rationalLE_congr
    (RationalAlgebra.multiply_commutative _ _) (RationalAlgebra.multiply_commutative _ _) multiplier
  exact RationalArgmin.transitive errorBound
    (add_monotone _ _ _ _ (residual_l1_bound step C N p q j hRD hC hm hN hp hpq hj) multiplier')


/-- Fixed PR5 reification of the actual scalar stage error. -/
def errorF (step : PR 3) : PR 5 := PTm.toPR
  (error step (var 0) (var 1) (var 2) (var 3) (var 4))

theorem error_program_at (step : PR 3) (C N p q j : PTm n) : Γ ⊢[PRAAx]
    PTm.app (errorF step) ![C,N,p,q,j] ≐ error step C N p q j := by
  simpa only [errorF,subst_error,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (error step (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,p,q,j]

theorem error_vector_length (step : PR 3) (C N p q j : PTm n) : Γ ⊢[PRAAx]
    length (errorCoefficients step C N p q j) ≐ succ (remaining N j) := GaussianCoefficientL1.zip_length _ _ _ _

theorem actual_error_step_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (monicRD step ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      le one (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶ lt (var 4) (var 1) ⟶
        rationalLE (error step (var 0) (var 1) (var 2) (var 3) (var 4))
          (add (fraction (two*var 2) (toleranceDenominator (var 0) (var 1) (var 3)))
            (multiply (natCode (GaussianFactorBudget.factor (var 1) (initialA (var 0)) (var 4)))
              (error step (var 0) (var 1) (var 2) (var 3) (succ (var 4)))))) := by
  apply closeUniv 5
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact error_step _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem actual_error_terminal_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶ le one (var 1) ⟶
      error step (var 0) (var 1) (var 2) (var 3) (var 1) ≐ natCode zero) :=
  closeUniv 4 (.impI (.impI (.impI (final_error_zero _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_error_initial_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (error step (var 0) (var 1) (var 2) (var 3) zero ≐ coefficientNorm
      (subCoefficients (var 0) (GaussianRationalReconstruction.reconstruct
        (roots step (var 0) (var 1) (var 2) (var 3) (var 1)) (var 1) (var 1)) (succ (var 1)))) :=
  closeUniv 4 (error_initial _ _ _ _ _)

theorem actual_error_nonnegative_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (RationalNormalForm.wellFormed (error step (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      rationalLE (natCode zero) (error step (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.andI (error_guard _ _ _ _ _ _) (error_nonnegative _ _ _ _ _ _))

theorem actual_error_program_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((PTm.app (errorF step) ![var 0,var 1,var 2,var 3,var 4] ≐
      error step (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        (length (errorCoefficients step (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
          succ (remaining (var 1) (var 4)))) :=
  closeUniv 5 (.andI (error_program_at _ _ _ _ _ _) (error_vector_length _ _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianFactorErrorStep
