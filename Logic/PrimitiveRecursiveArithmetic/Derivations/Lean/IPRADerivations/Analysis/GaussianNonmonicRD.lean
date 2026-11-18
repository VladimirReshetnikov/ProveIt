import IPRADerivations.Analysis.GaussianTranslatedNonconstant
import IPRADerivations.Analysis.GaussianMonicRD

/-!
# Constructed contraction for every nonconstant rational polynomial

The original descending list may have zero leading coefficients. Actual
translation preserves its nonconstant witness, so the existing dominant
displacement and zero-residual branch satisfy the original degree-N RD
contract without monicity, a nonzero leading coefficient, or a change of
degree. The step is literally the already constructed monic step. All
degrees, coefficient codes and query points are numerical inputs.

This proves the finite contraction. The travel estimate from an arbitrary
nonconstant coefficient, and the resulting general coefficient-name
iteration, remain separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNonmonicRD

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianBalancedRadius (inputContract)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslation (translated)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate canonical qadd)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq)
open LeanProofs.IPRA.Analysis.GaussianDescentClock (residualNumerator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def step : PR 3 := GaussianMonicRD.step
def delta (N C z : PTm n) : PTm n := GaussianMonicRD.delta N C z
def next (N C z : PTm n) : PTm n := GaussianMonicRD.next N C z

@[simp] theorem subst_delta {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    Syn.subst σ (delta N C z) = delta (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [delta]
@[simp] theorem subst_next {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    Syn.subst σ (next N C z) = next (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [next]

theorem positive_input (C N z : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residualNumerator C z)) : Γ ⊢[PRAAx]
    GaussianBalancedRadiusSyntax.input (translated C N z) N :=
  GaussianBalancedRadius.positive_input _ _
    (GaussianTranslatedNonconstant.translated_radius_input C N z hInput)
    (le_congr (.eqRefl _) (GaussianTranslatedBalancedRadius.residual_identity C N z).eqSymm hPositive)

/-- Translation and the actual dominant-term estimates discharge every
positive-branch obligation from the original nonconstant input. -/
theorem positive_decrease (C N z : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residualNumerator C z)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (qnormSq (evaluate C (qadd z (GaussianMonicPositiveDecrease.positiveDelta N C z))))
      (RationalArithmetic.multiply (GaussianDescentClock.contractionSquare N) (qnormSq (evaluate C z))) := by
  have decrease := GaussianDominantResidualEstimates.residual_decrease (translated C N z) N (positive_input C N z hInput hPositive)
  have evaluated := GaussianRationalTranslation.translation_evaluation C N z
    (GaussianMonicPositiveDecrease.positiveDelta N C z) (Prf.andE₁ hInput)
  have constant := GaussianRationalTranslation.ascending_constant (Γ := Γ) C N z
  exact RationalArgmin.rationalLE_congr (GaussianRationalProductWitness.qnormSq_congr evaluated)
    (RationalAlgebra.multiply_congr (GaussianMonicPositiveDecrease.contraction_clock N)
      (GaussianRationalProductWitness.qnormSq_congr constant)) decrease

theorem positive_program_decrease (C N z : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residualNumerator C z)) : Γ ⊢[PRAAx]
    GaussianMonicDescentBranch.positiveAt GaussianMonicRD.descent N C z :=
  RationalArgmin.rationalLE_congr
    (GaussianRationalProductWitness.qnormSq_congr
      (GaussianRationalTranslation.evaluate_congr (.eqRefl _)
        (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _)
          (GaussianMonicPositiveDecrease.positive_delta_at N C z).eqSymm)))
    (.eqRefl _) (positive_decrease C N z hInput hPositive)

theorem positive_local (N C : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N) : Γ ⊢[PRAAx]
    GaussianMonicDescentBranch.positiveLocal GaussianMonicRD.descent N C := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] inputContract (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianBalancedRadius.subst_inputContract,Syn.shift] using hInput.shift
  refine .allI (.impI (.impI ?_))
  exact positive_program_decrease (Syn.shift C) (Syn.shift N) (var 0) shifted.wk.wk Prf.hyp0

theorem local_rd (N C : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N) : Γ ⊢[PRAAx]
    GaussianDescentClock.localRD step N C :=
  GaussianMonicDescentBranch.local_rd_of_positive GaussianMonicRD.descent N C (positive_local N C hInput)

theorem actual_rd_at (N C z : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hz : Γ ⊢[PRAAx] canonical z) : Γ ⊢[PRAAx] GaussianDescentClock.rdAt step N C z :=
  GaussianDescentClock.local_rd_at step N C z (local_rd N C hInput) hz

def nonconstantRD : Fm PTm n := .all (.all
  (inputContract (var 0) (var 1) ⟶ GaussianDescentClock.localRD step (var 1) (var 0)))

theorem uniform_rd : Γ ⊢[PRAAx] (nonconstantRD : Fm PTm n) :=
  .allI (.allI (.impI (local_rd (var 1) (var 0) Prf.hyp0)))

theorem program_at (N C z : PTm n) : Γ ⊢[PRAAx] ap3 step N C z ≐ next N C z := GaussianMonicRD.program_at N C z
theorem advance_at (N C z : PTm n) : Γ ⊢[PRAAx] GaussianDescentClock.advance step N C z ≐ next N C z := GaussianMonicRD.advance_at N C z
theorem next_canonical (N C z : PTm n) : Γ ⊢[PRAAx] canonical (next N C z) := GaussianMonicRD.next_canonical N C z

theorem constructed_nonconstant_rd_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] nonconstantRD := uniform_rd

theorem constructed_nonconstant_local_rd_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (inputContract (var 1) (var 0) ⟶ GaussianDescentClock.localRD step (var 0) (var 1)) :=
  closeUniv 2 (.impI (local_rd _ _ Prf.hyp0))

theorem constructed_nonconstant_rd_at_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 1) (var 0) ⟶ canonical (var 2) ⟶ GaussianDescentClock.rdAt step (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (actual_rd_at _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_nonconstant_positive_decrease_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 0) (var 1) ⟶ le one (residualNumerator (var 0) (var 2)) ⟶
      RationalArgmin.rationalLE
        (qnormSq (evaluate (var 0) (qadd (var 2) (GaussianMonicPositiveDecrease.positiveDelta (var 1) (var 0) (var 2)))))
        (RationalArithmetic.multiply (GaussianDescentClock.contractionSquare (var 1)) (qnormSq (evaluate (var 0) (var 2))))) :=
  closeUniv 3 (.impI (.impI (positive_decrease _ _ _ Prf.hyp1 Prf.hyp0)))

theorem nonconstant_step_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 step (var 0) (var 1) (var 2) ≐ next (var 0) (var 1) (var 2)) ⋏
      (GaussianDescentClock.advance step (var 0) (var 1) (var 2) ≐ next (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (program_at _ _ _) (advance_at _ _ _))

end LeanProofs.IPRA.Analysis.GaussianNonmonicRD
