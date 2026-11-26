import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTATrajectory
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTACoefficientDrift

/-!
# Actual residual propagation along the changing-sample FTA program

The current residual bound is a legitimate local induction hypothesis.
The actual nonmonic descent, derived from the original name/apartness
input, contracts that residual at the actual next trajectory point.
At a next point in the computed disk, the proved coefficient drift then
gives the exact next B Q^(j+1) bound. No next residual, contraction,
nonconstancy, successful step or global trajectory invariant is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTAResidualStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants (B R qNum qDen QNum QDen)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTATrajectory (polynomial trajectory)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sourceInput)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianDescentClock (residualNumerator residualDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def amplitude (a : PR 3) (N x j : PTm n) : PTm n := B a x*pw (QNum N) j
def scale (N j : PTm n) : PTm n := pw (QDen N) j
def contractedNumerator (a : PR 3) (N x j : PTm n) : PTm n := qNum N*amplitude a N x j
def contractedDenominator (N j : PTm n) : PTm n := qDen N*scale N j
def currentBound (a : PR 3) (N h x j : PTm n) : Fm PTm n :=
  bounded (evaluate (polynomial a N h x j) (trajectory a N h x j)) (amplitude a N x j) (scale N j)

@[simp] theorem subst_amplitude {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N x j : PTm n) :
    Syn.subst σ (amplitude a N x j) = amplitude a (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ j) := by simp [amplitude]
@[simp] theorem subst_scale {m : ℕ} (σ : Fin n → PTm m) (N j : PTm n) :
    Syn.subst σ (scale N j) = scale (Syn.subst σ N) (Syn.subst σ j) := by simp [scale]
@[simp] theorem subst_contractedNumerator {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N x j : PTm n) :
    Syn.subst σ (contractedNumerator a N x j) = contractedNumerator a (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ j) := by simp [contractedNumerator]
@[simp] theorem subst_contractedDenominator {m : ℕ} (σ : Fin n → PTm m) (N j : PTm n) :
    Syn.subst σ (contractedDenominator N j) = contractedDenominator (Syn.subst σ N) (Syn.subst σ j) := by simp [contractedDenominator]
@[simp] theorem subst_currentBound {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    (currentBound a N h x j).subst σ = currentBound a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by simp [currentBound]

theorem scale_positive (N j : PTm n) : Γ ⊢[PRAAx] le one (scale N j) :=
  GaussianPolynomialPerturbation.power_positive _ _ (GaussianGeneralFTAConstants.QDen_positive N)
theorem contracted_denominator_positive (N j : PTm n) : Γ ⊢[PRAAx] le one (contractedDenominator N j) :=
  positive_product _ _ (GaussianGeneralFTAConstants.qDen_positive N) (scale_positive N j)

theorem source_degree (a : PR 3) (N k h x : PTm n) (hInput : Γ ⊢[PRAAx] sourceInput a N k h x) :
    Γ ⊢[PRAAx] le one N :=
  le_trans (Prf.andE₁ (Prf.andE₂ hInput)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hInput)))

theorem polynomial_input (a : PR 3) (N k h x j : PTm n) (hInput : Γ ⊢[PRAAx] sourceInput a N k h x) :
    Γ ⊢[PRAAx] GaussianBalancedRadius.inputContract (polynomial a N h x j) N :=
  .andI (GaussianGeneralFTATrajectory.polynomial_length a N h x j)
    (.andI (source_degree a N k h x hInput)
      (GaussianGeneralFTATrajectory.polynomial_nonconstant a N k h x j hInput))

/-- Every actual RD premise is obtained from the source and the actual program. -/
theorem trajectory_rd (a : PR 3) (N k h x j : PTm n) (hInput : Γ ⊢[PRAAx] sourceInput a N k h x) :
    Γ ⊢[PRAAx] GaussianDescentClock.rdAt GaussianNonmonicRD.step N
      (polynomial a N h x j) (trajectory a N h x j) :=
  GaussianNonmonicRD.actual_rd_at _ _ _ (polynomial_input a N k h x j hInput)
    (GaussianGeneralFTATrajectory.trajectory_canonical a N h x j)

theorem actual_contraction_cleared (a : PR 3) (N k h x j : PTm n)
    (hInput : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    le ((qDen N*qDen N)*residualNumerator (polynomial a N h x j) (trajectory a N h x (succ j))*
      (residualDenominator (polynomial a N h x j) (trajectory a N h x j)*
        residualDenominator (polynomial a N h x j) (trajectory a N h x j)))
      ((qNum N*qNum N)*residualNumerator (polynomial a N h x j) (trajectory a N h x j)*
        (residualDenominator (polynomial a N h x j) (trajectory a N h x (succ j))*
          residualDenominator (polynomial a N h x j) (trajectory a N h x (succ j)))) := by
  have rd := GaussianDescentClock.rd_to_cleared GaussianNonmonicRD.step N
    (polynomial a N h x j) (trajectory a N h x j) (trajectory_rd a N k h x j hInput)
  have next := (GaussianGeneralFTATrajectory.trajectory_advance (Γ := Γ) a N h x j).eqSymm
  have rn := GaussianDescentClock.residual_numerator_congr (polynomial a N h x j) next
  have dn := GaussianDescentClock.residual_denominator_congr (polynomial a N h x j) next
  exact le_congr (congrMul (congrMul (.eqRefl _) rn) (.eqRefl _))
    (congrMul (.eqRefl _) (congrMul dn dn)) rd

/-- Only the positive decoded denominator of the current actual Horner value
is cancelled. A zero current residual causes no exceptional branch. -/
theorem poststep_bound (a : PR 3) (N k h x j : PTm n)
    (hInput : Γ ⊢[PRAAx] sourceInput a N k h x)
    (hCurrent : Γ ⊢[PRAAx] currentBound a N h x j) : Γ ⊢[PRAAx]
    bounded (evaluate (polynomial a N h x j) (trajectory a N h x (succ j)))
      (contractedNumerator a N x j) (contractedDenominator N j) := by
  have current := (GaussianDescentClock.residual_bound_iff _ _ _ _ (scale_positive N j)).iffMp hCurrent
  have positive := GaussianDescentClock.residual_denominator_positive (Γ := Γ)
    (polynomial a N h x j) (trajectory a N h x j)
  have combined := GaussianDescentClock.combine_step (qDen N) (qNum N)
    (scale N j*scale N j) (amplitude a N x j*amplitude a N x j)
    (residualNumerator (polynomial a N h x j) (trajectory a N h x j))
    (residualNumerator (polynomial a N h x j) (trajectory a N h x (succ j)))
    (residualDenominator (polynomial a N h x j) (trajectory a N h x j)*
      residualDenominator (polynomial a N h x j) (trajectory a N h x j))
    (residualDenominator (polynomial a N h x j) (trajectory a N h x (succ j))*
      residualDenominator (polynomial a N h x j) (trajectory a N h x (succ j)))
    (positive_product _ _ positive positive) current (actual_contraction_cleared a N k h x j hInput)
  apply (GaussianDescentClock.residual_bound_iff _ _ _ _ (contracted_denominator_positive N j)).iffMpr
  exact le_congr (by unfold contractedDenominator; ipra_ring)
    (by unfold contractedNumerator; ipra_ring) combined

/-- The exact natural cross comparison expresses q+1/(8D)=Q without
requiring literal equality of any arbitrary original Gaussian code. -/
theorem next_radius_identity (a : PR 3) (N x j : PTm n) : Γ ⊢[PRAAx]
    ((amplitude a N x j*contractedDenominator N j+
      contractedNumerator a N x j*(QDen N*scale N j))*scale N (succ j)) ≐
      amplitude a N x (succ j)*((QDen N*scale N j)*contractedDenominator N j) := by
  have qf := natEq (GaussianGeneralFTARates.predecessor_form (Γ := Γ) (qDen N)
    (GaussianGeneralFTAConstants.qDen_positive N))
  have Qf := natEq (GaussianGeneralFTARates.predecessor_form (Γ := Γ) (QDen N)
    (GaussianGeneralFTAConstants.QDen_positive N))
  have ds := natEq (pw_succ (Γ := Γ) (QDen N) j)
  have ns := natEq (pw_succ (Γ := Γ) (QNum N) j)
  have twice : Γ ⊢[PRAAx] QDen N ≐ two*qDen N := .eqRefl _
  have tw := natEq twice
  simp only [amplitude,scale,contractedNumerator,contractedDenominator]
  apply deriveNat
  ipra_simps
  simp only [GaussianGeneralFTAConstants.qNum,GaussianGeneralFTAConstants.QNum] at *
  rw [ds,ns]
  linear_combination -(𝔞(B a x)*𝔞(pw (PTm.pred (QDen N)) j)*𝔞(pw (QDen N) j)^2*𝔞(QDen N))*
    (𝔞(QDen N)*qf-𝔞(qDen N)*Qf+tw)

theorem next_residual_bound (a : PR 3) (N k h x j : PTm n)
    (hInput : Γ ⊢[PRAAx] sourceInput a N k h x)
    (hCurrent : Γ ⊢[PRAAx] currentBound a N h x j)
    (hNextDisk : Γ ⊢[PRAAx] bounded (trajectory a N h x (succ j)) (R a N h x) one) :
    Γ ⊢[PRAAx] currentBound a N h x (succ j) := by
  have drift := GaussianGeneralFTACoefficientDrift.adjacent_evaluation_bound a N h x j
    (trajectory a N h x (succ j)) (Prf.andE₁ hInput) hNextDisk
  have reversed := GaussianRationalDistanceOrder.distance_symmetric _ _ _ _
    (GaussianGeneralFTACoefficientDrift.denominator_positive N j) drift
  have next := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _
    (GaussianGeneralFTACoefficientDrift.denominator_positive N j) (contracted_denominator_positive N j)
    reversed (poststep_bound a N k h x j hInput hCurrent)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (GaussianGeneralFTACoefficientDrift.denominator_positive N j)
      (contracted_denominator_positive N j)) (scale_positive N (succ j))
    (le_congr (.eqRefl _) (next_radius_identity a N x j) (le_refl _)) next

/-! Actual numerical outputs, with the finite apartness witness retained
only as a numerical hypothesis of their correctness statements. -/

def postValue (a : PR 3) (N h x j : PTm n) : PTm n :=
  evaluate (polynomial a N h x j) (trajectory a N h x (succ j))
def nextValue (a : PR 3) (N h x j : PTm n) : PTm n :=
  evaluate (polynomial a N h x (succ j)) (trajectory a N h x (succ j))
def output (a : PR 3) (N h x j : PTm n) : PTm n :=
  pairT (postValue a N h x j) (pairT (nextValue a N h x j)
    (pairT (contractedNumerator a N x j) (contractedDenominator N j)))
def outputF (a : PR 3) : PR 4 := PTm.toPR (output a (var 0) (var 1) (var 2) (var 3))
def run (a : PR 3) (N h x j : PTm n) : PTm n := PTm.app (outputF a) ![N,h,x,j]

@[simp] theorem subst_postValue {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (postValue a N h x j) = postValue a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by simp [postValue]
@[simp] theorem subst_nextValue {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (nextValue a N h x j) = nextValue a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by simp [nextValue]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (output a N h x j) = output a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (run a N h x j) = run a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx] run a N h x j ≐ output a N h x j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output a (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,h,x,j]
theorem returned_post_value (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    fstT (run a N h x j) ≐ postValue a N h x j :=
  (congrFst (program_at a N h x j)).eqTrans (fst_pair _ _)
theorem returned_next_value (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run a N h x j)) ≐ nextValue a N h x j :=
  (congrFst ((congrSnd (program_at a N h x j)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_numerator (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run a N h x j))) ≐ contractedNumerator a N x j :=
  (congrFst ((congrSnd ((congrSnd (program_at a N h x j)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run a N h x j))) ≐ contractedDenominator N j :=
  ((congrSnd ((congrSnd ((congrSnd (program_at a N h x j)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))

theorem returned_post_bound (a : PR 3) (N k h x j : PTm n)
    (hInput : Γ ⊢[PRAAx] sourceInput a N k h x)
    (hCurrent : Γ ⊢[PRAAx] currentBound a N h x j) : Γ ⊢[PRAAx]
    bounded (fstT (run a N h x j)) (fstT (sndT (sndT (run a N h x j))))
      (sndT (sndT (sndT (run a N h x j)))) :=
  GaussianRationalReciprocal.bound_congr (returned_post_value a N h x j).eqSymm
    (returned_numerator a N h x j).eqSymm (returned_denominator a N h x j).eqSymm
    (poststep_bound a N k h x j hInput hCurrent)
theorem returned_next_bound (a : PR 3) (N k h x j : PTm n)
    (hInput : Γ ⊢[PRAAx] sourceInput a N k h x)
    (hCurrent : Γ ⊢[PRAAx] currentBound a N h x j)
    (hNextDisk : Γ ⊢[PRAAx] bounded (trajectory a N h x (succ j)) (R a N h x) one) : Γ ⊢[PRAAx]
    bounded (fstT (sndT (run a N h x j))) (amplitude a N x (succ j)) (scale N (succ j)) :=
  GaussianRationalReciprocal.bound_congr (returned_next_value a N h x j).eqSymm (.eqRefl _) (.eqRefl _)
    (next_residual_bound a N k h x j hInput hCurrent hNextDisk)

theorem actual_trajectory_rd_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianDescentClock.rdAt GaussianNonmonicRD.step (var 0)
        (polynomial a (var 0) (var 2) (var 3) (var 4)) (trajectory a (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (trajectory_rd _ _ _ _ _ _ Prf.hyp0))
theorem actual_poststep_residual_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ currentBound a (var 0) (var 2) (var 3) (var 4) ⟶
      bounded (postValue a (var 0) (var 2) (var 3) (var 4))
        (contractedNumerator a (var 0) (var 3) (var 4)) (contractedDenominator (var 0) (var 4))) :=
  closeUniv 5 (.impI (.impI (poststep_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_next_residual_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ currentBound a (var 0) (var 2) (var 3) (var 4) ⟶
      bounded (trajectory a (var 0) (var 2) (var 3) (succ (var 4))) (R a (var 0) (var 2) (var 3)) one ⟶
        currentBound a (var 0) (var 2) (var 3) (succ (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (next_residual_bound _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_residual_step_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run a (var 0) (var 1) (var 2) (var 3) ≐ output a (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _ _)
theorem returned_poststep_residual_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ currentBound a (var 0) (var 2) (var 3) (var 4) ⟶
      bounded (fstT (run a (var 0) (var 2) (var 3) (var 4)))
        (fstT (sndT (sndT (run a (var 0) (var 2) (var 3) (var 4)))))
        (sndT (sndT (sndT (run a (var 0) (var 2) (var 3) (var 4)))))) :=
  closeUniv 5 (.impI (.impI (returned_post_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem returned_next_residual_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ currentBound a (var 0) (var 2) (var 3) (var 4) ⟶
      bounded (trajectory a (var 0) (var 2) (var 3) (succ (var 4))) (R a (var 0) (var 2) (var 3)) one ⟶
        bounded (fstT (sndT (run a (var 0) (var 2) (var 3) (var 4))))
          (amplitude a (var 0) (var 3) (succ (var 4))) (scale (var 0) (succ (var 4)))) :=
  closeUniv 5 (.impI (.impI (.impI (returned_next_bound _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGeneralFTAResidualStep
