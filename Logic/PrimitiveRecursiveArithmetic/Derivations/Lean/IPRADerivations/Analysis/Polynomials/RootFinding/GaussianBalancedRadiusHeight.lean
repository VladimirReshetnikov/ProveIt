import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianBalancedRadiusSyntax
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootSchedule
import IPRADerivations.Foundations.DemandClosure

/-!
# Actual finite bit-height for balanced Gaussian radius search

The polynomial is read in ascending degree through coefficient C N i. The
height is one plus an actual maximum fold over i=0,...,N of the bounded
binary lengths of the squared-norm numerator and its positive denominator.
This is an explicitly coarser choice than the source's component digit
height, retaining E=2b+3 and the later descent constant. All bounds are
derived from the original coefficient codes; none is supplied as an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBalancedRadiusHeight

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (coefficient numerator denominator three)
open LeanProofs.IPRA.Analysis.GaussianRootSchedule (binaryLength)
open LeanProofs.IPRA.Foundations.DemandClosure (maximum maximum_left maximum_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def bitHeight (C N i : PTm n) : PTm n := maximum
  (binaryLength (numerator C N i)) (binaryLength (denominator C N i))
def heightStep : PTm 4 := maximum (var 1) (bitHeight (var 2) (var 3) (var 0))
def heightF : PR 3 := recDef (zero : PTm 2) heightStep
def heightPrefix (C N j : PTm n) : PTm n := ap3 heightF j C N
def b (C N : PTm n) : PTm n := succ (heightPrefix C N (succ N))
def E (C N : PTm n) : PTm n := two*b C N+three

@[simp] theorem subst_bitHeight {m : ℕ} (σ : Fin n → PTm m) (C N i : PTm n) :
    Syn.subst σ (bitHeight C N i) = bitHeight (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ i) := by simp [bitHeight]
@[simp] theorem subst_prefix {m : ℕ} (σ : Fin n → PTm m) (C N j : PTm n) :
    Syn.subst σ (heightPrefix C N j) = heightPrefix (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ j) := by simp [heightPrefix]
@[simp] theorem subst_b {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (b C N) = b (Syn.subst σ C) (Syn.subst σ N) := by simp [b]
@[simp] theorem subst_E {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (E C N) = E (Syn.subst σ C) (Syn.subst σ N) := by simp [E]

theorem prefix_zero (C N : PTm n) : Γ ⊢[PRAAx] heightPrefix C N zero ≐ zero := by
  have h := rec_zero (Γ := Γ) (zero : PTm 2) heightStep ![C,N]
  have e : (Fin.cases zero ![C,N] : Fin 3 → PTm n) = ![zero,C,N] := by funext i; fin_cases i <;> rfl
  rw [e] at h
  simpa [heightPrefix,heightF,ap3] using h

theorem prefix_succ (C N j : PTm n) : Γ ⊢[PRAAx]
    heightPrefix C N (succ j) ≐ maximum (heightPrefix C N j) (bitHeight C N j) := by
  have h := rec_succ (Γ := Γ) (zero : PTm 2) heightStep j ![C,N]
  have a : (Fin.cases (succ j) ![C,N] : Fin 3 → PTm n) = ![succ j,C,N] := by funext i; fin_cases i <;> rfl
  have d : (Fin.cases j (Fin.cases (PTm.app (recDef (zero : PTm 2) heightStep) (Fin.cases j ![C,N])) ![C,N]) :
      Fin 4 → PTm n) = ![j,heightPrefix C N j,C,N] := by funext i; fin_cases i <;> rfl
  rw [a,d] at h
  simpa only [heightPrefix,heightF,ap3,heightStep,Foundations.DemandClosure.subst_maximum,subst_bitHeight,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using h

theorem prefix_step_monotone (C N j : PTm n) : Γ ⊢[PRAAx] le (heightPrefix C N j) (heightPrefix C N (succ j)) :=
  le_congr (.eqRefl _) (prefix_succ C N j).eqSymm (maximum_left _ _)
theorem prefix_last_bound (C N j : PTm n) : Γ ⊢[PRAAx] le (bitHeight C N j) (heightPrefix C N (succ j)) :=
  le_congr (.eqRefl _) (prefix_succ C N j).eqSymm (maximum_right _ _)

def entryLaw (C N i j : PTm n) : Fm PTm n := lt i j ⟶ le (bitHeight C N i) (heightPrefix C N j)
@[simp] theorem subst_entryLaw {m : ℕ} (σ : Fin n → PTm m) (C N i j : PTm n) :
    (entryLaw C N i j).subst σ = entryLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ i) (Syn.subst σ j) := by
  simp [entryLaw]

theorem prefix_entry_step (C N i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ j))
    (ih : Γ ⊢[PRAAx] entryLaw C N i j) : Γ ⊢[PRAAx] le (bitHeight C N i) (heightPrefix C N (succ j)) := by
  have bound : Γ ⊢[PRAAx] le i j := (succ_monus_succ _ _).eqSymm.eqTrans hi
  refine .orE (lt_or_eq_of_le bound) ?_ ?_
  · exact le_trans (.impE ih.wk Prf.hyp0) (prefix_step_monotone C N j)
  · have index := Prf.eqCongr (Ax := PRAAx) (Γ := (i ≐ j)::Γ) (bitHeight (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![C,N,i]) (σ' := ![C,N,j]) (fun k => by fin_cases k; exact .eqRefl _; exact .eqRefl _; exact Prf.hyp0)
    have changed : (i ≐ j)::Γ ⊢[PRAAx] bitHeight C N i ≐ bitHeight C N j := by
      simpa only [subst_bitHeight,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.head_cons,Matrix.tail_cons] using index
    exact le_congr changed.eqSymm (.eqRefl _) (prefix_last_bound C N j)

/-- Genuine quantifier-free induction bounds every entry of the actual
maximum fold; the numerical heightPrefix length is not fixed externally. -/
theorem prefix_entry_bound (C N i j : PTm n) (hi : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    le (bitHeight C N i) (heightPrefix C N j) := by
  have all : Γ ⊢[PRAAx] .all (entryLaw (Syn.shift C) (Syn.shift N) (Syn.shift i) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_entryLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (lt_zero_absurd _ Prf.hyp0)
    · simp only [subst_entryLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (prefix_entry_step _ _ _ _ Prf.hyp0 Prf.hyp1)
  have rule : Γ ⊢[PRAAx] entryLaw C N i j := by
    simpa only [subst_entryLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hi

theorem b_positive (C N : PTm n) : Γ ⊢[PRAAx] le one (b C N) :=
  le_of_eq_add (d := heightPrefix C N (succ N)) (by unfold b; ipra_ring)

theorem bit_height_bound (C N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] le (bitHeight C N i) (b C N) :=
  le_trans (prefix_entry_bound C N i (succ N) ((succ_monus_succ i N).eqTrans hi)) (le_succ_self _)

theorem numerator_bit_bound (C N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    le (binaryLength (numerator C N i)) (b C N) :=
  le_trans (maximum_left _ _) (bit_height_bound C N i hi)
theorem denominator_bit_bound (C N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    le (binaryLength (denominator C N i)) (b C N) :=
  le_trans (maximum_right _ _) (bit_height_bound C N i hi)

theorem numerator_bound (C N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    le (numerator C N i) (pw two (b C N)) :=
  le_trans (Prf.andE₁ (GaussianRootSchedule.binary_length_correct _))
    (GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (numerator_bit_bound C N i hi))
theorem denominator_bound (C N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    le (denominator C N i) (pw two (b C N)) :=
  le_trans (Prf.andE₁ (GaussianRootSchedule.binary_length_correct _))
    (GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (denominator_bit_bound C N i hi))

theorem denominator_positive (C N i : PTm n) : Γ ⊢[PRAAx] le one (denominator C N i) :=
  GaussianBalancedRadiusSyntax.denominator_positive C N i

theorem E_definition (C N : PTm n) : Γ ⊢[PRAAx] E C N ≐ two*b C N+three := .eqRefl _

def allBounds (C N : PTm n) : Fm PTm n := .all (le (var 0) (Syn.shift N) ⟶
  (le (numerator (Syn.shift C) (Syn.shift N) (var 0)) (pw two (b (Syn.shift C) (Syn.shift N))) ⋏
   (le one (denominator (Syn.shift C) (Syn.shift N) (var 0)) ⋏
    le (denominator (Syn.shift C) (Syn.shift N) (var 0)) (pw two (b (Syn.shift C) (Syn.shift N))))))
@[simp] theorem subst_allBounds {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    (allBounds C N).subst σ = allBounds (Syn.subst σ C) (Syn.subst σ N) := by
  simp [allBounds,Syn.subst_shift,Syn.shift_subst]

theorem all_bounds (C N : PTm n) : Γ ⊢[PRAAx] allBounds C N := by
  refine .allI (.impI ?_)
  exact .andI (numerator_bound (Syn.shift C) (Syn.shift N) (var 0) Prf.hyp0)
    (.andI (denominator_positive _ _ _) (denominator_bound (Syn.shift C) (Syn.shift N) (var 0) Prf.hyp0))

/-! Actual PR2 output and returned numerical fields. -/
def output (C N : PTm n) : PTm n := pairT (b C N) (pairT (E C N) (pw two (b C N)))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (output C N) = output (Syn.subst σ C) (Syn.subst σ N) := by simp [output]

theorem program_at (C N : PTm n) : Γ ⊢[PRAAx] ap2 outputF C N ≐ output C N := by
  simpa [outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![C,N]

theorem returned_height (C N : PTm n) : Γ ⊢[PRAAx] fstT (ap2 outputF C N) ≐ b C N :=
  (congrFst (program_at C N)).eqTrans (fst_pair _ _)
theorem returned_exponent (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (ap2 outputF C N)) ≐ E C N :=
  (congrFst ((congrSnd (program_at C N)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_bound (C N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (ap2 outputF C N)) ≐ pw two (b C N) :=
  (congrSnd ((congrSnd (program_at C N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem height_facts_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (b (var 0) (var 1)) ⋏
      (E (var 0) (var 1) ≐ two*b (var 0) (var 1)+three ⋏ allBounds (var 0) (var 1))) :=
  closeUniv 2 (.andI (b_positive _ _) (.andI (E_definition _ _) (all_bounds _ _)))

theorem coefficient_height_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 1) ⟶
      (le (numerator (var 0) (var 1) (var 2)) (pw two (b (var 0) (var 1))) ⋏
       (le one (denominator (var 0) (var 1) (var 2)) ⋏
        le (denominator (var 0) (var 1) (var 2)) (pw two (b (var 0) (var 1)))))) :=
  closeUniv 3 (.impI (.andI (numerator_bound _ _ _ Prf.hyp0)
    (.andI (denominator_positive _ _ _) (denominator_bound _ _ _ Prf.hyp0))))

theorem maxfold_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((heightPrefix (var 0) (var 1) zero ≐ zero) ⋏
      (heightPrefix (var 0) (var 1) (succ (var 2)) ≐
        maximum (heightPrefix (var 0) (var 1) (var 2)) (bitHeight (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (prefix_zero _ _) (prefix_succ _ _ _))

theorem height_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 outputF (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)

theorem returned_height_metadata_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (fstT (ap2 outputF (var 0) (var 1))) ⋏
      ((fstT (ap2 outputF (var 0) (var 1)) ≐ b (var 0) (var 1)) ⋏
       ((fstT (sndT (ap2 outputF (var 0) (var 1))) ≐ E (var 0) (var 1)) ⋏
        (sndT (sndT (ap2 outputF (var 0) (var 1))) ≐ pw two (b (var 0) (var 1)))))) :=
  closeUniv 2 (.andI (le_congr (.eqRefl _) (returned_height _ _).eqSymm (b_positive _ _))
    (.andI (returned_height _ _) (.andI (returned_exponent _ _) (returned_bound _ _))))

end LeanProofs.IPRA.Analysis.GaussianBalancedRadiusHeight
