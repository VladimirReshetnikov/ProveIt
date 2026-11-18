import IPRADerivations.Analysis.GaussianZeroResidualContraction
import IPRADerivations.Analysis.GaussianFactorParameters
import IPRADerivations.Analysis.GaussianRationalProductWitness
import IPRADerivations.Combinatorics.FiniteBijection

/-!
# Actual zero/positive residual branching for rational descent

The computed residual numerator selects the literal zero increment or the
supplied increment program. The actual clock update is proved to stay at
an already zero canonical point. A local positive-branch derivation then
suffices for the full local RD contract. This adapter does not assert the
positive decrease law of an arbitrary program: that legitimate local law
remains explicit until instantiated by the concrete checked producer.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianMonicDescentBranch

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qadd qzero canonical)
open LeanProofs.IPRA.Analysis.GaussianDescentClock
  (advance residualNumerator contractionSquare rdAt localRD)
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.Probability.MedianCounts (congrSg)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def flag (C z : PTm n) : PTm n := sg (residualNumerator C z)
def branchDelta (descent : PR 3) (N C z : PTm n) : PTm n :=
  RationalArithmetic.select (flag C z) qzero (ap3 descent N C z)
def branchDeltaF (descent : PR 3) : PR 3 := PTm.toPR (branchDelta descent (var 0) (var 1) (var 2))
def step (descent : PR 3) : PR 3 := GaussianDescentClock.incrementStep (branchDeltaF descent)

@[simp] theorem subst_flag {m : ℕ} (σ : Fin n → PTm m) (C z : PTm n) :
    Syn.subst σ (flag C z) = flag (Syn.subst σ C) (Syn.subst σ z) := by simp [flag]
@[simp] theorem subst_branchDelta {m : ℕ} (σ : Fin n → PTm m) (descent : PR 3) (N C z : PTm n) :
    Syn.subst σ (branchDelta descent N C z) = branchDelta descent (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [branchDelta]

theorem flag_boolean (C z : PTm n) : Γ ⊢[PRAAx] (flag C z ≐ zero) ⋎ (flag C z ≐ one) :=
  Combinatorics.FiniteBijection.sg_bit _
theorem flag_zero (C z : PTm n) (h : Γ ⊢[PRAAx] residualNumerator C z ≐ zero) : Γ ⊢[PRAAx] flag C z ≐ zero :=
  (congrSg h).eqTrans sg_zero
theorem flag_positive (C z : PTm n) (h : Γ ⊢[PRAAx] le one (residualNumerator C z)) : Γ ⊢[PRAAx] flag C z ≐ one :=
  (congrSg (RationalIntegerNormalization.positive_form h)).eqTrans (sg_succ _)

theorem branch_zero (descent : PR 3) (N C z : PTm n) (h : Γ ⊢[PRAAx] residualNumerator C z ≐ zero) : Γ ⊢[PRAAx]
    branchDelta descent N C z ≐ qzero := RationalArithmetic.select_zero _ _ _ (flag_zero C z h)
theorem branch_positive (descent : PR 3) (N C z : PTm n) (h : Γ ⊢[PRAAx] le one (residualNumerator C z)) : Γ ⊢[PRAAx]
    branchDelta descent N C z ≐ ap3 descent N C z := RationalArithmetic.select_one _ _ _ (flag_positive C z h)

theorem branch_at (descent : PR 3) (N C z : PTm n) : Γ ⊢[PRAAx]
    ap3 (branchDeltaF descent) N C z ≐ branchDelta descent N C z := by
  simpa [branchDeltaF,ap3] using toPR_eq (Γ := Γ) (branchDelta descent (var 0) (var 1) (var 2) : PTm 3) ![N,C,z]

theorem advance_branch (descent : PR 3) (N C z : PTm n) : Γ ⊢[PRAAx]
    advance (step descent) N C z ≐ qadd z (branchDelta descent N C z) :=
  (GaussianDescentClock.advance_increment _ _ _ _).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (branch_at descent N C z))

theorem advance_zero (descent : PR 3) (N C z : PTm n) (hz : Γ ⊢[PRAAx] canonical z)
    (h0 : Γ ⊢[PRAAx] residualNumerator C z ≐ zero) : Γ ⊢[PRAAx] advance (step descent) N C z ≐ z :=
  (advance_branch descent N C z).eqTrans
    ((GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (branch_zero descent N C z h0)).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right z hz))
theorem advance_positive (descent : PR 3) (N C z : PTm n)
    (h0 : Γ ⊢[PRAAx] le one (residualNumerator C z)) : Γ ⊢[PRAAx]
    advance (step descent) N C z ≐ qadd z (ap3 descent N C z) :=
  (advance_branch descent N C z).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (branch_positive descent N C z h0))

def positiveAt (descent : PR 3) (N C z : PTm n) : Fm PTm n := RationalArgmin.rationalLE
  (GaussianRationalMetric.qnormSq (evaluate C (qadd z (ap3 descent N C z))))
  (RationalArithmetic.multiply (contractionSquare N) (GaussianRationalMetric.qnormSq (evaluate C z)))
def positiveLocal (descent : PR 3) (N C : PTm n) : Fm PTm n :=
  .all (canonical (var 0) ⟶ le one (residualNumerator (Syn.shift C) (var 0)) ⟶
    positiveAt descent (Syn.shift N) (Syn.shift C) (var 0))
def positiveMonic (descent : PR 3) : Fm PTm n := .all (.all
  (le one (var 1) ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ GaussianRationalSyntheticDivision.qone ⟶
    positiveLocal descent (var 1) (var 0)))

@[simp] theorem subst_positiveAt {m : ℕ} (σ : Fin n → PTm m) (descent : PR 3) (N C z : PTm n) :
    (positiveAt descent N C z).subst σ = positiveAt descent (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [positiveAt]
@[simp] theorem subst_positiveLocal {m : ℕ} (σ : Fin n → PTm m) (descent : PR 3) (N C : PTm n) :
    (positiveLocal descent N C).subst σ = positiveLocal descent (Syn.subst σ N) (Syn.subst σ C) := by
  simp [positiveLocal,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_positiveMonic {m : ℕ} (σ : Fin n → PTm m) (descent : PR 3) :
    (positiveMonic descent : Fm PTm n).subst σ = (positiveMonic descent : Fm PTm m) := by simp [positiveMonic]

theorem rd_at (descent : PR 3) (N C z : PTm n) (hz : Γ ⊢[PRAAx] canonical z)
    (hPositive : Γ ⊢[PRAAx] le one (residualNumerator C z) ⟶ positiveAt descent N C z) : Γ ⊢[PRAAx]
    rdAt (step descent) N C z := by
  refine .orE (zero_or_succ (residualNumerator C z)) ?_ ?_
  · have value := GaussianRationalProductWitness.qnormSq_congr
      (GaussianRationalTranslation.evaluate_congr (.eqRefl C) (advance_zero descent N C z hz.wk Prf.hyp0))
    exact RationalArgmin.rationalLE_congr value.eqSymm (.eqRefl _)
      (GaussianZeroResidualContraction.zero_contraction N C z Prf.hyp0)
  · have pos : (residualNumerator C z ≐ succ (PTm.pred (residualNumerator C z)))::Γ ⊢[PRAAx]
        le one (residualNumerator C z) := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have value := GaussianRationalProductWitness.qnormSq_congr
      (GaussianRationalTranslation.evaluate_congr (.eqRefl C) (advance_positive descent N C z pos))
    exact RationalArgmin.rationalLE_congr value.eqSymm (.eqRefl _) (.impE hPositive.wk pos)

theorem positive_local_at (descent : PR 3) (N C z : PTm n)
    (h : Γ ⊢[PRAAx] positiveLocal descent N C) (hz : Γ ⊢[PRAAx] canonical z) : Γ ⊢[PRAAx]
    le one (residualNumerator C z) ⟶ positiveAt descent N C z := by
  have rule : Γ ⊢[PRAAx] canonical z ⟶ le one (residualNumerator C z) ⟶ positiveAt descent N C z := by
    simpa [positiveLocal] using h.allE z
  exact .impE rule hz

theorem local_rd_of_positive (descent : PR 3) (N C : PTm n) (h : Γ ⊢[PRAAx] positiveLocal descent N C) : Γ ⊢[PRAAx]
    localRD (step descent) N C := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] positiveLocal descent (Syn.shift N) (Syn.shift C) := by
    simpa only [Fm.shift,subst_positiveLocal,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  exact rd_at descent (Syn.shift N) (Syn.shift C) (var 0) Prf.hyp0
    (positive_local_at _ _ _ _ shifted.wk Prf.hyp0)

theorem monic_rd_of_positive (descent : PR 3) (h : Γ ⊢[PRAAx] positiveMonic descent) : Γ ⊢[PRAAx]
    GaussianFactorParameters.monicRD (step descent) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] (positiveMonic descent : Fm PTm (n+2)) := by
    simpa only [Fm.shift,subst_positiveMonic] using h.shift.shift
  refine .allI (.allI (.impI (.impI (.impI ?_))))
  have rule : (((entry (var 0) zero ≐ GaussianRationalSyntheticDivision.qone)::
      (length (var 0) ≐ succ (var 1))::(le one (var 1))::(Γ.map Fm.shift).map Fm.shift) : List (Fm PTm (n+2))) ⊢[PRAAx]
      le one (var 1) ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ GaussianRationalSyntheticDivision.qone ⟶
        positiveLocal descent (var 1) (var 0) := by
    simpa [positiveMonic] using (hs.wk.wk.wk.allE (var 1)).allE (var 0)
  exact local_rd_of_positive descent _ _ (.impE (.impE (.impE rule Prf.hyp0.wk.wk) Prf.hyp1) Prf.hyp0)

theorem actual_branch_program_closed (descent : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 (branchDeltaF descent) (var 0) (var 1) (var 2) ≐ branchDelta descent (var 0) (var 1) (var 2)) :=
  closeUniv 3 (branch_at _ _ _ _)
theorem actual_zero_branch_closed (descent : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (canonical (var 2) ⟶ residualNumerator (var 1) (var 2) ≐ zero ⟶ advance (step descent) (var 0) (var 1) (var 2) ≐ var 2) :=
  closeUniv 3 (.impI (.impI (advance_zero _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_positive_branch_closed (descent : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (residualNumerator (var 1) (var 2)) ⟶
      advance (step descent) (var 0) (var 1) (var 2) ≐ qadd (var 2) (ap3 descent (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (advance_positive _ _ _ _ Prf.hyp0))
theorem derived_local_rd_closed (descent : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (positiveLocal descent (var 0) (var 1) ⟶ localRD (step descent) (var 0) (var 1)) :=
  closeUniv 2 (.impI (local_rd_of_positive _ _ _ Prf.hyp0))
theorem derived_monic_rd_closed (descent : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    positiveMonic descent ⟶ GaussianFactorParameters.monicRD (step descent) :=
  .impI (monic_rd_of_positive _ Prf.hyp0)

end LeanProofs.IPRA.Analysis.GaussianMonicDescentBranch
