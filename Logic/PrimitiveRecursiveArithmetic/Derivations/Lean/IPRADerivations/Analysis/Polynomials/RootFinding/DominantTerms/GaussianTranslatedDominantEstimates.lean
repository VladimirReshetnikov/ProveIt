import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianRationalDominantDecomposition
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantMagnitude

/-!
# Actual original-polynomial decomposition and dominant estimates

The original monic list, degree and point determine the translated list,
plateau, dominant term and remaining sum. The original value at z+delta
is literally their checked normalized sum, with constant exactly P(z).
The same computed dominant score has the exact source upper/lower bounds,
and the off-dominant norm estimate holds for every displacement in the
computed radius. Both original residual branches are retained.

No translated list, decomposition, positive maximum, lower bound, sum
estimate or successful search is an input. Actual direction construction
and the dominant-pair decrease remain separate obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianTranslatedDominantEstimates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qadd)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslation (translated)
open LeanProofs.IPRA.Analysis.GaussianTranslatedBalancedRadius (inputContract residual)
open LeanProofs.IPRA.Analysis.GaussianDominantPlateau (winner)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (descentD)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def dominant (C N z delta : PTm n) : PTm n := GaussianOffDominantTerms.term
  (translated C N z) N delta (winner (translated C N z) N)
def otherSum (C N z delta : PTm n) : PTm n := GaussianOffDominantSum.otherSum (translated C N z) N delta
def score (C N z : PTm n) : PTm n := GaussianOffDominantSum.selectedScore (translated C N z) N
def disk (C N z delta : PTm n) : Fm PTm n := GaussianOffDominantTerms.withinRadius (translated C N z) N delta
def decomposition (C N z delta : PTm n) : Fm PTm n :=
  evaluate C (qadd z delta) ≐ qadd (qadd (evaluate C z) (dominant C N z delta)) (otherSum C N z delta)
def magnitude (C N z : PTm n) : Fm PTm n :=
  neg (RationalArgmin.rationalLE (score C N z) (fraction zero one)) ⋏
    (RationalArgmin.rationalLE (score C N z) (GaussianRationalMetric.qnormSq (evaluate C z)) ⋏
      neg (RationalArgmin.rationalLE (GaussianDominantMagnitude.multiple (GaussianDominantMagnitude.squaredBudget N) (score C N z))
        (GaussianRationalMetric.qnormSq (evaluate C z))))
def certificate (C N z delta : PTm n) : Fm PTm n := decomposition C N z delta ⋏
  (magnitude C N z ⋏
    (disk C N z delta ⟶ GaussianOffDominantSum.bound (translated C N z) N delta))
def prepared (C N z delta : PTm n) : Fm PTm n :=
  (residual C z ≐ zero ⟶ GaussianTranslatedBalancedRadius.radius C N z ≐ fraction zero one) ⋏
    (le one (residual C z) ⟶ certificate C N z delta)

@[simp] theorem subst_dominant {m : ℕ} (σ : Fin n → PTm m) (C N z delta : PTm n) :
    Syn.subst σ (dominant C N z delta) = dominant (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ delta) := by simp [dominant]
@[simp] theorem subst_otherSum {m : ℕ} (σ : Fin n → PTm m) (C N z delta : PTm n) :
    Syn.subst σ (otherSum C N z delta) = otherSum (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ delta) := by simp [otherSum]
@[simp] theorem subst_score {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (score C N z) = score (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [score]
@[simp] theorem subst_disk {m : ℕ} (σ : Fin n → PTm m) (C N z delta : PTm n) :
    (disk C N z delta).subst σ = disk (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ delta) := by simp [disk]
@[simp] theorem subst_decomposition {m : ℕ} (σ : Fin n → PTm m) (C N z delta : PTm n) :
    (decomposition C N z delta).subst σ = decomposition (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ delta) := by simp [decomposition]
@[simp] theorem subst_magnitude {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    (magnitude C N z).subst σ = magnitude (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [magnitude]
@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (C N z delta : PTm n) :
    (certificate C N z delta).subst σ = certificate (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ delta) := by simp [certificate]
@[simp] theorem subst_prepared {m : ℕ} (σ : Fin n → PTm m) (C N z delta : PTm n) :
    (prepared C N z delta).subst σ = prepared (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ delta) := by simp [prepared]

theorem translated_split (C N z delta k : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    evaluate C (qadd z delta) ≐
      qadd (qadd (evaluate C z) (GaussianOffDominantTerms.term (translated C N z) N delta k))
        (GaussianGeometricSumBound.otherSum (GaussianOffDominantTerms.lowerList (translated C N z) N delta k)
          (GaussianOffDominantTerms.upperList (translated C N z) N delta k)) :=
  (GaussianRationalTranslation.translation_evaluation C N z delta hLen).eqSymm.eqTrans
    ((GaussianRationalDominantDecomposition.dominant_decomposition _ _ _ _
      (GaussianRationalTranslation.translated_length C N z) hk hkN).eqTrans
      (qadd_congr (qadd_congr (GaussianTranslatedBalancedRadius.constant_coefficient C N z) (.eqRefl _)) (.eqRefl _)))

theorem original_decomposition (C N z delta : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx] decomposition C N z delta := by
  have shape := GaussianTranslatedDominantPlateau.positive_input C N z hInput hPositive
  have bounds := GaussianDominantPlateau.winner_bounds (translated C N z) N shape
  exact translated_split C N z delta (winner (translated C N z) N) (Prf.andE₁ hInput) (Prf.andE₁ bounds) (Prf.andE₂ bounds)

theorem constant_score_identity (C N z : PTm n) : Γ ⊢[PRAAx]
    GaussianDominantMagnitude.constantScore (translated C N z) N ≐ GaussianRationalMetric.qnormSq (evaluate C z) :=
  GaussianRationalProductWitness.qnormSq_congr (GaussianTranslatedBalancedRadius.constant_coefficient C N z)

theorem original_magnitude (C N z : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx] magnitude C N z := by
  have shape := GaussianTranslatedDominantPlateau.positive_input C N z hInput hPositive
  have identity := constant_score_identity (Γ := Γ) C N z
  refine .andI (GaussianDominantMagnitude.selected_positive _ _ shape) (.andI ?_ ?_)
  · exact RationalArgmin.rationalLE_congr (.eqRefl _) identity (GaussianDominantMagnitude.dominant_upper _ _ shape)
  · refine .impI ?_
    exact .impE (GaussianDominantMagnitude.dominant_lower _ _ shape).wk
      (RationalArgmin.rationalLE_congr (.eqRefl _) identity.wk.eqSymm Prf.hyp0)

theorem original_estimates (C N z delta : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx] certificate C N z delta :=
  .andI (original_decomposition C N z delta hInput hPositive)
    (.andI (original_magnitude C N z hInput hPositive)
      (.impI (GaussianOffDominantSum.original_input_bound C N z delta hInput.wk hPositive.wk Prf.hyp0)))

/-- Under only the original monic shape, retain the zero branch and
derive every positive-branch preparation at any original displacement. -/
theorem original_preparation (C N z delta : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N) : Γ ⊢[PRAAx]
    prepared C N z delta :=
  .andI (.impI (GaussianTranslatedBalancedRadius.zero_radius C N z Prf.hyp0))
    (.impI (original_estimates C N z delta hInput.wk Prf.hyp0))

def output (C N z delta : PTm n) : PTm n := pairT (evaluate C (qadd z delta))
  (pairT (evaluate C z) (pairT (dominant C N z delta) (pairT (otherSum C N z delta) (pairT (score C N z) (descentD N)))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (C N z delta : PTm n) : PTm n := PTm.app outputF ![C,N,z,delta]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N z delta : PTm n) :
    Syn.subst σ (output C N z delta) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ delta) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N z delta : PTm n) :
    Syn.subst σ (run C N z delta) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ delta) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (C N z delta : PTm n) : Γ ⊢[PRAAx] run C N z delta ≐ output C N z delta := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,z,delta]
theorem returned_evaluation (C N z delta : PTm n) : Γ ⊢[PRAAx] fstT (run C N z delta) ≐ evaluate C (qadd z delta) :=
  (congrFst (program_at C N z delta)).eqTrans (fst_pair _ _)
theorem returned_constant (C N z delta : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N z delta)) ≐ evaluate C z :=
  (congrFst ((congrSnd (program_at C N z delta)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_dominant (C N z delta : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N z delta))) ≐ dominant C N z delta :=
  (congrFst ((congrSnd ((congrSnd (program_at C N z delta)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_other (C N z delta : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run C N z delta)))) ≐ otherSum C N z delta :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at C N z delta)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_score (C N z delta : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run C N z delta))))) ≐ score C N z :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at C N z delta)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_budget (C N z delta : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run C N z delta))))) ≐ descentD N :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at C N z delta)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem returned_decomposition (C N z delta : PTm n) (hInput : Γ ⊢[PRAAx] inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (residual C z)) : Γ ⊢[PRAAx]
    fstT (run C N z delta) ≐ qadd (qadd (fstT (sndT (run C N z delta)))
      (fstT (sndT (sndT (run C N z delta))))) (fstT (sndT (sndT (sndT (run C N z delta))))) :=
  (returned_evaluation C N z delta).eqTrans ((original_decomposition C N z delta hInput hPositive).eqTrans
    (qadd_congr (qadd_congr (returned_constant C N z delta).eqSymm (returned_dominant C N z delta).eqSymm)
      (returned_other C N z delta).eqSymm))

theorem original_dominant_estimates_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract (var 0) (var 1) ⟶ le one (residual (var 0) (var 2)) ⟶
      certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (original_estimates _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_dominant_preparation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract (var 0) (var 1) ⟶ prepared (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (original_preparation _ _ _ _ Prf.hyp0))
theorem original_dominant_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem returned_original_decomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract (var 0) (var 1) ⟶ le one (residual (var 0) (var 2)) ⟶
      let t := run (var 0) (var 1) (var 2) (var 3)
      fstT t ≐ qadd (qadd (fstT (sndT t)) (fstT (sndT (sndT t)))) (fstT (sndT (sndT (sndT t))))) :=
  closeUniv 4 (.impI (.impI (returned_decomposition _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_magnitude_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract (var 0) (var 1) ⟶ le one (residual (var 0) (var 2)) ⟶ magnitude (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (original_magnitude _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianTranslatedDominantEstimates
