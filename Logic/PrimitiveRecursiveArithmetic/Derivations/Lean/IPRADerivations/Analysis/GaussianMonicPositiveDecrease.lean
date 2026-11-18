import IPRADerivations.Analysis.GaussianDominantResidualEstimates
import IPRADerivations.Analysis.GaussianTranslatedDominantPlateau
import IPRADerivations.Analysis.GaussianDescentClock

/-!
# Original monic polynomial decrease at its actual positive displacement

The original polynomial and point determine the translated list and actual
displacement. Original monicity and a positive evaluated residual supply all
balanced-input guards. The literal translation and constant-coefficient
identities transport the proved contraction to the original evaluator and
identify its exact factor with the existing descent clock.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianMonicPositiveDecrease

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalTranslation (translated)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qadd evaluate canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq)
open LeanProofs.IPRA.Analysis.GaussianTranslatedBalancedRadius (inputContract residual)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (descentD rateDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def positiveDelta (N C z : PTm n) : PTm n := GaussianDominantResidualEstimates.delta (translated C N z) N
def positiveNext (N C z : PTm n) : PTm n := qadd z (positiveDelta N C z)
def radiusNumerator (N C z : PTm n) : PTm n := GaussianOffDominantTerms.radiusNumerator (translated C N z) N
def radiusDenominator (N C z : PTm n) : PTm n := GaussianOffDominantTerms.radiusDenominator (translated C N z) N

@[simp] theorem subst_positiveDelta {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    Syn.subst σ (positiveDelta N C z) = positiveDelta (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [positiveDelta]
@[simp] theorem subst_positiveNext {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    Syn.subst σ (positiveNext N C z) = positiveNext (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [positiveNext]
@[simp] theorem subst_radiusNumerator {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    Syn.subst σ (radiusNumerator N C z) = radiusNumerator (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [radiusNumerator]
@[simp] theorem subst_radiusDenominator {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    Syn.subst σ (radiusDenominator N C z) = radiusDenominator (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [radiusDenominator]

theorem rate_den_clock (N : PTm n) : Γ ⊢[PRAAx]
    GaussianResidualDecreaseWeights.rateDen (descentD N) ≐ rateDenominator N := .eqRefl _

theorem rate_num_clock (N : PTm n) : Γ ⊢[PRAAx]
    GaussianResidualDecreaseWeights.rateNum (descentD N) ≐ pred (rateDenominator N) :=
  (monus_succ (rateDenominator N) zero).eqTrans (congrPred (monus_zero _))

theorem contraction_clock (N : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.squaredTolerance (GaussianResidualDecreaseWeights.rateNum (descentD N))
      (GaussianResidualDecreaseWeights.rateDen (descentD N)) ≐ GaussianDescentClock.contractionSquare N :=
  GaussianRationalThreeTermBudget.tolerance_congr (rate_num_clock N) (rate_den_clock N)

theorem positive_delta_canonical (N C z : PTm n) : Γ ⊢[PRAAx] canonical (positiveDelta N C z) :=
  GaussianRationalHorner.qmul_canonical _ _

theorem positive_next_canonical (N C z : PTm n) : Γ ⊢[PRAAx] canonical (positiveNext N C z) :=
  GaussianRationalHorner.qadd_canonical _ _

theorem positive_delta_radius (N C z : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (positiveDelta N C z) (radiusNumerator N C z) (radiusDenominator N C z) :=
  GaussianDominantResidualEstimates.delta_inside _ _

theorem radius_denominator_positive (N C z : PTm n) : Γ ⊢[PRAAx] le one (radiusDenominator N C z) :=
  GaussianOffDominantTerms.radius_denominator_positive _ _

/-- Only the original monic input and positive evaluated residual are
assumed. Translation, direction, term estimates and contraction are derived. -/
theorem positive_decrease (C N z : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (evaluate C (qadd z (positiveDelta N C z))))
      (RationalArithmetic.multiply (GaussianDescentClock.contractionSquare N) (qnormSq (evaluate C z))) := by
  have input := GaussianTranslatedDominantPlateau.positive_input C N z hInput hPositive
  have decrease := GaussianDominantResidualEstimates.residual_decrease (translated C N z) N input
  have evaluated := GaussianRationalTranslation.translation_evaluation C N z (positiveDelta N C z) (Prf.andE₁ hInput)
  have constant := GaussianRationalTranslation.ascending_constant (Γ := Γ) C N z
  exact RationalArgmin.rationalLE_congr (GaussianRationalProductWitness.qnormSq_congr evaluated)
    (RationalAlgebra.multiply_congr (contraction_clock N) (GaussianRationalProductWitness.qnormSq_congr constant)) decrease

/-! The displacement program uses the original argument order N,C,z. -/
def deltaF : PR 3 := PTm.toPR (positiveDelta (var 0) (var 1) (var 2))

theorem positive_delta_at (N C z : PTm n) : Γ ⊢[PRAAx] ap3 deltaF N C z ≐ positiveDelta N C z := by
  simpa [deltaF,ap3] using toPR_eq (Γ := Γ) (positiveDelta (var 0) (var 1) (var 2) : PTm 3) ![N,C,z]

theorem positive_program_decrease (C N z : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (evaluate C (qadd z (ap3 deltaF N C z))))
      (RationalArithmetic.multiply (GaussianDescentClock.contractionSquare N) (qnormSq (evaluate C z))) :=
  RationalArgmin.rationalLE_congr
    (GaussianRationalProductWitness.qnormSq_congr
      (GaussianRationalTranslation.evaluate_congr (.eqRefl _)
        (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (positive_delta_at N C z).eqSymm)))
    (.eqRefl _) (positive_decrease C N z hInput hPositive)

theorem delta_program_canonical (N C z : PTm n) : Γ ⊢[PRAAx] canonical (ap3 deltaF N C z) :=
  GaussianRationalHorner.canonical_congr (positive_delta_at N C z) (positive_delta_canonical N C z)

theorem delta_program_radius (N C z : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (ap3 deltaF N C z) (radiusNumerator N C z) (radiusDenominator N C z) :=
  GaussianRationalReciprocal.bound_congr (positive_delta_at N C z).eqSymm (.eqRefl _) (.eqRefl _)
    (positive_delta_radius N C z)

def output (N C z : PTm n) : PTm n := pairT (positiveDelta N C z)
  (pairT (positiveNext N C z) (pairT (evaluate C (positiveNext N C z))
    (pairT (radiusNumerator N C z) (radiusDenominator N C z))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (N C z : PTm n) : PTm n := ap3 outputF N C z

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    Syn.subst σ (output N C z) = output (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    Syn.subst σ (run N C z) = run (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [run]

theorem program_at (N C z : PTm n) : Γ ⊢[PRAAx] run N C z ≐ output N C z := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![N,C,z]

theorem returned_delta (N C z : PTm n) : Γ ⊢[PRAAx] fstT (run N C z) ≐ positiveDelta N C z :=
  (congrFst (program_at N C z)).eqTrans (fst_pair _ _)
theorem returned_point (N C z : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run N C z)) ≐ positiveNext N C z :=
  (congrFst ((congrSnd (program_at N C z)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_value (N C z : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run N C z))) ≐ evaluate C (positiveNext N C z) :=
  (congrFst ((congrSnd ((congrSnd (program_at N C z)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_radius_num (N C z : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run N C z)))) ≐ radiusNumerator N C z :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at N C z)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_radius_den (N C z : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run N C z)))) ≐ radiusDenominator N C z :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at N C z)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_decrease (C N z : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq (fstT (sndT (sndT (run N C z)))))
      (RationalArithmetic.multiply (GaussianDescentClock.contractionSquare N) (qnormSq (evaluate C z))) :=
  RationalArgmin.rationalLE_congr
    (GaussianRationalProductWitness.qnormSq_congr (returned_value N C z).eqSymm) (.eqRefl _)
    (positive_decrease C N z hInput hPositive)

theorem original_positive_decrease_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 0) (var 1) ⟶ le one (residual (var 0) (var 2)) ⟶
      RationalArgmin.rationalLE
        (qnormSq (evaluate (var 0) (qadd (var 2) (positiveDelta (var 1) (var 0) (var 2)))))
        (RationalArithmetic.multiply (GaussianDescentClock.contractionSquare (var 1)) (qnormSq (evaluate (var 0) (var 2))))) :=
  closeUniv 3 (.impI (.impI (positive_decrease _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_positive_program_decrease_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 0) (var 1) ⟶ le one (residual (var 0) (var 2)) ⟶
      RationalArgmin.rationalLE
        (qnormSq (evaluate (var 0) (qadd (var 2) (ap3 deltaF (var 1) (var 0) (var 2)))))
        (RationalArithmetic.multiply (GaussianDescentClock.contractionSquare (var 1)) (qnormSq (evaluate (var 0) (var 2))))) :=
  closeUniv 3 (.impI (.impI (positive_program_decrease _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_positive_delta_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 deltaF (var 0) (var 1) (var 2) ≐ positiveDelta (var 0) (var 1) (var 2)) ⋏
      (canonical (ap3 deltaF (var 0) (var 1) (var 2)) ⋏
        GaussianRationalMetric.bounded (ap3 deltaF (var 0) (var 1) (var 2))
          (radiusNumerator (var 0) (var 1) (var 2)) (radiusDenominator (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (positive_delta_at _ _ _) (.andI (delta_program_canonical _ _ _) (delta_program_radius _ _ _)))

theorem actual_positive_trace_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)

theorem returned_original_decrease_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 0) (var 1) ⟶ le one (residual (var 0) (var 2)) ⟶
      RationalArgmin.rationalLE (qnormSq (fstT (sndT (sndT (run (var 1) (var 0) (var 2))))))
        (RationalArithmetic.multiply (GaussianDescentClock.contractionSquare (var 1)) (qnormSq (evaluate (var 0) (var 2))))) :=
  closeUniv 3 (.impI (.impI (returned_decrease _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianMonicPositiveDecrease
