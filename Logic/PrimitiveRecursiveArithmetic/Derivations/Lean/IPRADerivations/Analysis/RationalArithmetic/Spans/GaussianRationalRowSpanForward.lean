import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalRowSpanPivotForward
import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalRowSpanRewind
import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticSubspaceFromSpan
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual forward coefficients through rectangular elimination

The numerical recursion follows the original matrix/history prefixes.
Skipped columns retain the weights, and a successful pivot uses the
actual one-step forward coefficients. A guarded QF invariant preserves
one arbitrary original column, then gives exact field membership and
the original existential finite-coefficient statement.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRowSpanForward

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalEliminationLoop (matrix history matrix_zero matrix_succ matrix_shape)
open GaussianRationalPivotSearch (flag selected flag_cases next_failure next_success selected_input)
open GaussianRationalRowElimination (shape)
open GaussianRationalRowSpan (combinationAt combination_lookup membership membership_at)
open GaussianRationalRowSpanRewind (combination_congr)
open GaussianSuperellipticSubspaceFromSpan (hasCoefficients)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_zero sel_one)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def advance (A R N c u : PTm n) : PTm n :=
  let E := matrix A R N c
  let H := history A R N c
  sel (flag E R H c c) (GaussianRationalRowSpanPivotForward.forward E R u (selected E R H c c) c) u
def data (A R N u : PTm n) : PTm n := pairT u (pairT A (pairT R N))
def baseBody : PTm 1 := fstT (var 0)
def stepBody : PTm 3 := advance (fstT (sndT (var 2))) (fstT (sndT (sndT (var 2))))
  (sndT (sndT (sndT (var 2)))) (var 0) (var 1)
def weightsF : PR 2 := rec2 baseBody stepBody
def weights (A R N u c : PTm n) : PTm n := ap2 weightsF c (data A R N u)

@[simp] theorem subst_advance {k : ℕ} (σ : Fin n → PTm k) (A R N c u : PTm n) :
    Syn.subst σ (advance A R N c u) = advance (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ c) (Syn.subst σ u) := by simp [advance,sel]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (A R N u : PTm n) :
    Syn.subst σ (data A R N u) = data (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ u) := by simp [data]
@[simp] theorem subst_weights {k : ℕ} (σ : Fin n → PTm k) (A R N u c : PTm n) :
    Syn.subst σ (weights A R N u c) = weights (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ u) (Syn.subst σ c) := by simp [weights]

theorem advance_congr {A A' R R' N N' c c' u u' : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A')
    (hR : Γ ⊢[PRAAx] R ≐ R') (hN : Γ ⊢[PRAAx] N ≐ N') (hc : Γ ⊢[PRAAx] c ≐ c')
    (hu : Γ ⊢[PRAAx] u ≐ u') : Γ ⊢[PRAAx] advance A R N c u ≐ advance A' R' N' c' u' := by
  ipra_congr (advance (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hA, hR, hN, hc, hu]

theorem weights_zero (A R N u : PTm n) : Γ ⊢[PRAAx] weights A R N u zero ≐ u := by
  have e := rec2_zero (Γ := Γ) baseBody stepBody (data A R N u)
  simp only [baseBody,subst_fstT,Syn.subst_var] at e
  exact e.eqTrans (fst_pair _ _)
theorem weights_succ (A R N u c : PTm n) : Γ ⊢[PRAAx]
    weights A R N u (succ c) ≐ advance A R N c (weights A R N u c) := by
  have e := rec2_succ (Γ := Γ) baseBody stepBody c (data A R N u)
  simp only [stepBody,subst_advance,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at e
  have tail := snd_pair (Γ := Γ) u (pairT A (pairT R N))
  have dims := (congrSnd tail).eqTrans (snd_pair A (pairT R N))
  exact e.eqTrans (advance_congr ((congrFst tail).eqTrans (fst_pair _ _))
    ((congrFst dims).eqTrans (fst_pair _ _)) ((congrSnd dims).eqTrans (snd_pair _ _)) (.eqRefl _) (.eqRefl _))

theorem advance_length (A R N c u : PTm n) (hu : Γ ⊢[PRAAx] length u ≐ R) : Γ ⊢[PRAAx]
    length (advance A R N c u) ≐ R := by
  let E := matrix A R N c
  let H := history A R N c
  refine .orE (flag_cases E R H c c) ?_ ?_
  · exact (congrFst (sel_zero Prf.hyp0)).eqTrans hu.wk
  · exact (congrFst (sel_one Prf.hyp0)).eqTrans (GaussianRationalRowSpanPivotForward.forward_length E R u (selected E R H c c) c)
theorem weights_length (A R N u c : PTm n) (hu : Γ ⊢[PRAAx] length u ≐ R) : Γ ⊢[PRAAx]
    length (weights A R N u c) ≐ R := by
  have all : Γ ⊢[PRAAx] .all (length (weights (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift u) (var 0)) ≐ Syn.shift R) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_length,subst_weights,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (congrFst (weights_zero _ _ _ _)).eqTrans hu
    · simp only [Fm.subst_eq,subst_length,subst_weights,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (congrFst (weights_succ _ _ _ _ _)).eqTrans (advance_length _ _ _ _ _ Prf.hyp0)
  simpa only [Fm.subst_eq,subst_length,subst_weights,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE c

theorem advance_column (A R N c u j : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] lt c N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt (matrix A R N (succ c)) R (advance A R N c u) j ≐ combinationAt (matrix A R N c) R u j := by
  let E := matrix A R N c
  let H := history A R N c
  have step := matrix_succ (Γ := Γ) A R N c
  refine .orE (flag_cases E R H c c) ?_ ?_
  · have stayed := step.wk.eqTrans (next_failure E R N H c c Prf.hyp0)
    exact combination_congr stayed (sel_zero Prf.hyp0)
  · have changed := step.wk.eqTrans (next_success E R N H c c Prf.hyp0)
    exact (combination_congr changed (sel_one Prf.hyp0)).eqTrans
      (GaussianRationalRowSpanPivotForward.column_forward E R N u (selected E R H c c) c j
        (selected_input E R N H c c (matrix_shape A R N c hA.wk) hc.wk Prf.hyp0) hj.wk)

def columnLaw (A R N u j c : PTm n) : Fm PTm n := le c N ⟶
  combinationAt (matrix A R N c) R (weights A R N u c) j ≐ combinationAt A R u j
@[simp] theorem subst_columnLaw {k : ℕ} (σ : Fin n → PTm k) (A R N u j c : PTm n) :
    (columnLaw A R N u j c).subst σ = columnLaw (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ u) (Syn.subst σ j) (Syn.subst σ c) := by simp [columnLaw]
theorem column_step (A R N u j c : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hj : Γ ⊢[PRAAx] lt j N) (hc : Γ ⊢[PRAAx] le (succ c) N)
    (ih : Γ ⊢[PRAAx] columnLaw A R N u j c) : Γ ⊢[PRAAx]
    combinationAt (matrix A R N (succ c)) R (weights A R N u (succ c)) j ≐ combinationAt A R u j :=
  (combination_congr (.eqRefl _) (weights_succ A R N u c)).eqTrans
    ((advance_column A R N c (weights A R N u c) j hA hc hj).eqTrans
      (.impE ih (le_trans (le_succ_self _) hc)))

theorem column_forward (A R N u c j : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] le c N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt (matrix A R N c) R (weights A R N u c) j ≐ combinationAt A R u j := by
  have As : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalRowElimination.subst_shape,Syn.shift] using hA.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  have all : Γ ⊢[PRAAx] .all (columnLaw (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift u) (Syn.shift j) (var 0)) := by
    refine PRA.qfInd _ (by simp [columnLaw,Fm.QF,le]) ?_ ?_
    · simp only [subst_columnLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (combination_congr (matrix_zero _ _ _) (weights_zero _ _ _ _))
    · simp only [subst_columnLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (column_step (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift u) (Syn.shift j)
        (var 0) As.wk.wk js.wk.wk Prf.hyp0 Prf.hyp1)
  have atC : Γ ⊢[PRAAx] columnLaw A R N u j c := by
    simpa only [subst_columnLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE c
  exact .impE atC hc

theorem membership_forward (A R N u v c : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] le c N) (hm : Γ ⊢[PRAAx] membership A R N u v) : Γ ⊢[PRAAx]
    membership (matrix A R N c) R N (weights A R N u c) v := by
  have As : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalRowElimination.subst_shape,Syn.shift] using hA.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift c) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hc.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift u) (Syn.shift v) := by
    simpa only [Fm.shift,GaussianRationalRowSpan.subst_membership,Syn.shift] using hm.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have old := membership_at (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift u) (Syn.shift v) (var 0) ms.wk Prf.hyp0
  have target := (combination_lookup (Γ := Δ) (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c))
    (Syn.shift R) (Syn.shift N) (weights (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift u) (Syn.shift c)) (var 0) Prf.hyp0).eqTrans
      ((column_forward _ _ _ _ _ _ As.wk cs.wk Prf.hyp0).eqTrans (combination_lookup _ _ _ _ _ Prf.hyp0).eqSymm)
  simpa only [Δ,Syn.shift,GaussianRationalEliminationLoop.subst_matrix,subst_weights] using
    GaussianRationalValueEquality.value_equal_trans _ _ _ old (GaussianRationalValueEquality.value_equal_of_code target.eqSymm)

theorem hasCoefficients_forward (A R N v c : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] le c N) (hm : Γ ⊢[PRAAx] hasCoefficients A R N v) : Γ ⊢[PRAAx]
    hasCoefficients (matrix A R N c) R N v := by
  have As : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalRowElimination.subst_shape,Syn.shift] using hA.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift c) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hc.shift
  refine .exE hm ?_
  let Δ := ((length (var 0) ≐ Syn.shift R) ⋏ membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift v)) :: Γ.map Fm.shift
  have hl := weights_length (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift c) (.andE₁ Prf.hyp0)
  have mem := membership_forward (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift v) (Syn.shift c)
    As.wk cs.wk (.andE₂ Prf.hyp0)
  have out : Δ ⊢[PRAAx] hasCoefficients (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c))
      (Syn.shift R) (Syn.shift N) (Syn.shift v) := by
    refine .exI (weights (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift c)) ?_
    simpa only [hasCoefficients,Fm.subst_and,Fm.subst_eq,subst_length,GaussianRationalRowSpan.subst_membership,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hl mem
  simpa only [Δ,Fm.shift,GaussianSuperellipticSubspaceFromSpan.subst_hasCoefficients,
    GaussianRationalEliminationLoop.subst_matrix,Syn.shift] using out

def outputF : PR 5 := PTm.toPR (weights (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A R N u c : PTm n) : PTm n := app outputF ![A,R,N,u,c]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (A R N u c : PTm n) :
    Syn.subst σ (run A R N u c) = run (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ u) (Syn.subst σ c) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl
theorem program_at (A R N u c : PTm n) : Γ ⊢[PRAAx] run A R N u c ≐ weights A R N u c := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (weights (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,R,N,u,c]
theorem returned_length (A R N u c : PTm n) (hu : Γ ⊢[PRAAx] length u ≐ R) : Γ ⊢[PRAAx]
    length (run A R N u c) ≐ R := (congrFst (program_at _ _ _ _ _)).eqTrans (weights_length _ _ _ _ _ hu)
theorem returned_column (A R N u c j : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hc : Γ ⊢[PRAAx] le c N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt (matrix A R N c) R (run A R N u c) j ≐ combinationAt A R u j :=
  (combination_congr (.eqRefl _) (program_at A R N u c)).eqTrans (column_forward A R N u c j hA hc hj)

theorem actual_forward_weights_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 3) ≐ var 1 ⟶ length (weights (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ var 1) :=
  closeUniv 5 (.impI (weights_length _ _ _ _ _ Prf.hyp0))
theorem actual_forward_column_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (shape (var 0) (var 1) (var 2) ⟶ le (var 4) (var 2) ⟶ lt (var 5) (var 2) ⟶
      combinationAt (matrix (var 0) (var 1) (var 2) (var 4)) (var 1)
        (weights (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐ combinationAt (var 0) (var 1) (var 3) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (column_forward _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_membership_forward_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (shape (var 0) (var 1) (var 2) ⟶ le (var 5) (var 2) ⟶ membership (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      membership (matrix (var 0) (var 1) (var 2) (var 5)) (var 1) (var 2)
        (weights (var 0) (var 1) (var 2) (var 3) (var 5)) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (membership_forward _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_existential_membership_forward_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (shape (var 0) (var 1) (var 2) ⟶ le (var 4) (var 2) ⟶ hasCoefficients (var 0) (var 1) (var 2) (var 3) ⟶
      hasCoefficients (matrix (var 0) (var 1) (var 2) (var 4)) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (hasCoefficients_forward _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ weights (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_column_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (shape (var 0) (var 1) (var 2) ⟶ le (var 4) (var 2) ⟶ lt (var 5) (var 2) ⟶
      combinationAt (matrix (var 0) (var 1) (var 2) (var 4)) (var 1)
        (run (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐ combinationAt (var 0) (var 1) (var 3) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (returned_column _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalRowSpanForward
