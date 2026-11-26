import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFiniteSum
import IPRADerivations.Core.MultiSums

/-!
# Interchanging actual finite Gaussian-rational sums

A fixed three-variable syntax body supplies a matrix entry at numerical
row, column and data. The two nested sums are separately constructed
GaussianRationalFiniteSum programs. A genuine quantifier-free induction
on the outer row count proves their equality using bounded entry
congruence and the actual sum-addition theorem. Both counts and the
persistent data remain internal, including either empty dimension.

Original entries may be arbitrary raw Gaussian-rational codes. They
remain under qadd in the recurrence; only actual sum outputs are used
as canonical values. No natural-code addition, host-sized matrix,
supplied interchange law or equality of generated list codes is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFubini

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qadd_congr qzero_canonical qzero_add)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum
  (sum sum_canonical sum_index_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- At column j and packed data (i,x), read the original entry a(i,j,x). -/
def rowBody (a : PTm 3) : PTm 2 := Syn.subst ![fstT (var 1),var 0,sndT (var 1)] a

/-- At row i and packed data (j,x), read the same original entry a(i,j,x). -/
def columnBody (a : PTm 3) : PTm 2 := Syn.subst ![var 0,fstT (var 1),sndT (var 1)] a

@[simp] theorem row_body_at (a : PTm 3) (j z : PTm n) :
    inst2 (rowBody a) j z = inst3 a (fstT z) j (sndT z) := by
  simp only [inst2,inst3,rowBody,Syn.subst_subst]
  congr 1
  funext i
  fin_cases i <;> simp

@[simp] theorem column_body_at (a : PTm 3) (i z : PTm n) :
    inst2 (columnBody a) i z = inst3 a i (fstT z) (sndT z) := by
  simp only [inst2,inst3,columnBody,Syn.subst_subst]
  congr 1
  funext j
  fin_cases j <;> simp

theorem row_entry (a : PTm 3) (i j x : PTm n) : Γ ⊢[PRAAx]
    inst2 (rowBody a) j (pairT i x) ≐ inst3 a i j x := by
  rw [row_body_at]
  exact congrInst3 a (fst_pair _ _) (.eqRefl _) (snd_pair _ _)

theorem column_entry (a : PTm 3) (i j x : PTm n) : Γ ⊢[PRAAx]
    inst2 (columnBody a) i (pairT j x) ≐ inst3 a i j x := by
  rw [column_body_at]
  exact congrInst3 a (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

def row (a : PTm 3) (i M x : PTm n) : PTm n := sum (rowBody a) M (pairT i x)
def column (a : PTm 3) (j N x : PTm n) : PTm n := sum (columnBody a) N (pairT j x)

@[simp] theorem subst_row {l : ℕ} (σ : Fin n → PTm l) (a : PTm 3) (i M x : PTm n) :
    Syn.subst σ (row a i M x) = row a (Syn.subst σ i) (Syn.subst σ M) (Syn.subst σ x) := by simp [row]
@[simp] theorem subst_column {l : ℕ} (σ : Fin n → PTm l) (a : PTm 3) (j N x : PTm n) :
    Syn.subst σ (column a j N x) = column a (Syn.subst σ j) (Syn.subst σ N) (Syn.subst σ x) := by simp [column]

theorem row_zero (a : PTm 3) (i x : PTm n) : Γ ⊢[PRAAx] row a i zero x ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
theorem column_zero (a : PTm 3) (j x : PTm n) : Γ ⊢[PRAAx] column a j zero x ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
theorem row_succ (a : PTm 3) (i M x : PTm n) : Γ ⊢[PRAAx]
    row a i (succ M) x ≐ qadd (row a i M x) (inst3 a i M x) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (row_entry a i M x))
theorem column_succ (a : PTm 3) (j N x : PTm n) : Γ ⊢[PRAAx]
    column a j (succ N) x ≐ qadd (column a j N x) (inst3 a N j x) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (column_entry a N j x))

/-- Both inner bodies use the actual sum program, not natural addition. -/
def rowSumBody (a : PTm 3) : PTm 2 :=
  sum (rowBody a) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))
def columnSumBody (a : PTm 3) : PTm 2 :=
  sum (columnBody a) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

@[simp] theorem row_sum_body_at (a : PTm 3) (i z : PTm n) :
    inst2 (rowSumBody a) i z = row a i (fstT z) (sndT z) := by simp [inst2,rowSumBody,row]
@[simp] theorem column_sum_body_at (a : PTm 3) (j z : PTm n) :
    inst2 (columnSumBody a) j z = column a j (fstT z) (sndT z) := by simp [inst2,columnSumBody,column]

theorem row_sum_at (a : PTm 3) (i M x : PTm n) : Γ ⊢[PRAAx]
    inst2 (rowSumBody a) i (pairT M x) ≐ row a i M x := by
  rw [row_sum_body_at]
  exact sum_index_congr _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
theorem column_sum_at (a : PTm 3) (j N x : PTm n) : Γ ⊢[PRAAx]
    inst2 (columnSumBody a) j (pairT N x) ≐ column a j N x := by
  rw [column_sum_body_at]
  exact sum_index_congr _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

def rowFirst (a : PTm 3) (N M x : PTm n) : PTm n := sum (rowSumBody a) N (pairT M x)
def columnFirst (a : PTm 3) (N M x : PTm n) : PTm n := sum (columnSumBody a) M (pairT N x)

@[simp] theorem subst_rowFirst {l : ℕ} (σ : Fin n → PTm l) (a : PTm 3) (N M x : PTm n) :
    Syn.subst σ (rowFirst a N M x) = rowFirst a (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ x) := by simp [rowFirst]
@[simp] theorem subst_columnFirst {l : ℕ} (σ : Fin n → PTm l) (a : PTm 3) (N M x : PTm n) :
    Syn.subst σ (columnFirst a N M x) = columnFirst a (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ x) := by simp [columnFirst]

theorem row_first_canonical (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx] canonical (rowFirst a N M x) := sum_canonical _ _ _
theorem column_first_canonical (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx] canonical (columnFirst a N M x) := sum_canonical _ _ _

/-- This auxiliary zero sum concerns actual canonical zero entries. -/
theorem zero_body_sum (M x : PTm n) : Γ ⊢[PRAAx] sum (qzero : PTm 2) M x ≐ qzero := by
  have all : Γ ⊢[PRAAx] .all (sum (qzero : PTm 2) (var 0) (Syn.shift x) ≐ qzero) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,Syn.subst_var,Syn.inst_zero,
        Syn.subst_inst_shift,GaussianRationalHorner.subst_qzero]
      exact GaussianRationalFiniteSum.sum_zero _ _
    · simp only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,Syn.subst_var,Syn.repl_zero,
        subst_repl_shift,GaussianRationalHorner.subst_qzero]
      have next := GaussianRationalFiniteSum.sum_succ (Γ := (sum (qzero : PTm 2) (var 0) (Syn.shift x) ≐ qzero) :: Γ.map Fm.shift)
        (qzero : PTm 2) (var 0) (Syn.shift x)
      have z : inst2 (qzero : PTm 2) (var 0 : PTm (n+1)) (Syn.shift x) = qzero := by simp [inst2]
      rw [z] at next
      exact next.eqTrans ((qadd_congr Prf.hyp0 (.eqRefl _)).eqTrans (qzero_add qzero qzero_canonical))
  simpa only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,Syn.subst_var,Syn.inst_zero,
    Syn.subst_inst_shift,GaussianRationalHorner.subst_qzero] using all.allE M

theorem row_first_zero_rows (a : PTm 3) (M x : PTm n) : Γ ⊢[PRAAx] rowFirst a zero M x ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
theorem column_first_zero_columns (a : PTm 3) (N x : PTm n) : Γ ⊢[PRAAx] columnFirst a N zero x ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _

theorem row_first_zero_columns (a : PTm 3) (N x : PTm n) : Γ ⊢[PRAAx] rowFirst a N zero x ≐ qzero := by
  refine (GaussianRationalFiniteSum.sum_congr_bounded (rowSumBody a) (qzero : PTm 2) N (pairT zero x) x ?_).eqTrans (zero_body_sum N x)
  refine .allI (.impI ?_)
  have z : inst2 (qzero : PTm 2) (var 0 : PTm (n+1)) (Syn.shift x) = qzero := by simp [inst2]
  rw [z,shift_pairT]
  simpa only [Syn.shift,ConciseIPRA.PTm.subst_zero] using
    (row_sum_at a (var 0) zero (Syn.shift x)).eqTrans (row_zero a (var 0) (Syn.shift x))

theorem column_first_zero_rows (a : PTm 3) (M x : PTm n) : Γ ⊢[PRAAx] columnFirst a zero M x ≐ qzero := by
  refine (GaussianRationalFiniteSum.sum_congr_bounded (columnSumBody a) (qzero : PTm 2) M (pairT zero x) x ?_).eqTrans (zero_body_sum M x)
  refine .allI (.impI ?_)
  have z : inst2 (qzero : PTm 2) (var 0 : PTm (n+1)) (Syn.shift x) = qzero := by simp [inst2]
  rw [z,shift_pairT]
  simpa only [Syn.shift,ConciseIPRA.PTm.subst_zero] using
    (column_sum_at a (var 0) zero (Syn.shift x)).eqTrans (column_zero a (var 0) (Syn.shift x))

theorem row_first_succ (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx]
    rowFirst a (succ N) M x ≐ qadd (rowFirst a N M x) (row a N M x) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (row_sum_at a N M x))
theorem column_first_succ (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx]
    columnFirst a N (succ M) x ≐ qadd (columnFirst a N M x) (column a M N x) :=
  (GaussianRationalFiniteSum.sum_succ _ _ _).eqTrans (qadd_congr (.eqRefl _) (column_sum_at a M N x))

/-- The new raw row entry remains under qadd at each actual column. -/
theorem column_append_at (a : PTm 3) (N j x : PTm n) : Γ ⊢[PRAAx]
    inst2 (columnSumBody a) j (pairT (succ N) x) ≐
      inst2 (GaussianRationalFiniteSum.addBody (columnSumBody a) (rowBody a)) j (pairT N x) := by
  rw [GaussianRationalFiniteSum.inst2_addBody]
  exact (column_sum_at a j (succ N) x).eqTrans ((column_succ a j N x).eqTrans
    (qadd_congr (column_sum_at a j N x) (row_entry a N j x)).eqSymm)

theorem column_first_append_row (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx]
    columnFirst a (succ N) M x ≐ qadd (columnFirst a N M x) (row a N M x) := by
  refine (GaussianRationalFiniteSum.sum_congr_bounded (columnSumBody a) (GaussianRationalFiniteSum.addBody (columnSumBody a) (rowBody a)) M
    (pairT (succ N) x) (pairT N x) ?_).eqTrans (GaussianRationalFiniteSum.sum_add _ _ _ _)
  refine .allI (.impI ?_)
  rw [shift_pairT,shift_pairT]
  simpa only [Syn.shift,ConciseIPRA.PTm.subst_succ] using column_append_at a (Syn.shift N) (var 0) (Syn.shift x)

def interchangeLaw (a : PTm 3) (N M x : PTm n) : Fm PTm n := rowFirst a N M x ≐ columnFirst a N M x
@[simp] theorem subst_interchangeLaw {l : ℕ} (σ : Fin n → PTm l) (a : PTm 3) (N M x : PTm n) :
    (interchangeLaw a N M x).subst σ = interchangeLaw a (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ x) := by
  simp only [interchangeLaw,Fm.subst_eq,subst_rowFirst,subst_columnFirst]

theorem interchange_zero (a : PTm 3) (M x : PTm n) : Γ ⊢[PRAAx] interchangeLaw a zero M x :=
  (row_first_zero_rows a M x).eqTrans (column_first_zero_rows a M x).eqSymm

theorem interchange_step (a : PTm 3) (N M x : PTm n) (ih : Γ ⊢[PRAAx] interchangeLaw a N M x) :
    Γ ⊢[PRAAx] interchangeLaw a (succ N) M x :=
  (row_first_succ a N M x).eqTrans ((qadd_congr ih (.eqRefl _)).eqTrans (column_first_append_row a N M x).eqSymm)

/-- Both dimensions and data are numerical; only the entry syntax is fixed. -/
theorem fubini (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx] rowFirst a N M x ≐ columnFirst a N M x := by
  have all : Γ ⊢[PRAAx] .all (interchangeLaw a (var 0) (Syn.shift M) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_interchangeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact interchange_zero a M x
    · simp only [subst_interchangeLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact interchange_step a _ _ _ Prf.hyp0
  have actual : Γ ⊢[PRAAx] interchangeLaw a N M x := by
    simpa only [subst_interchangeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact actual

/-- The payload contains the independently built row-first and column-first sums. -/
def output (a : PTm 3) (N M x : PTm n) : PTm n := pairT (rowFirst a N M x) (columnFirst a N M x)
def outputF (a : PTm 3) : PR 3 := PTm.toPR (output a (var 0) (var 1) (var 2))
def run (a : PTm 3) (N M x : PTm n) : PTm n := ap3 (outputF a) N M x
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (a : PTm 3) (N M x : PTm n) :
    Syn.subst σ (output a N M x) = output a (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (a : PTm 3) (N M x : PTm n) :
    Syn.subst σ (run a N M x) = run a (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ x) := by simp only [run,subst_ap3]

theorem program_at (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx] run a N M x ≐ output a N M x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output a (var 0) (var 1) (var 2) : PTm 3) ![N,M,x]
theorem returned_rows (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx] fstT (run a N M x) ≐ rowFirst a N M x :=
  (congrFst (program_at a N M x)).eqTrans (fst_pair _ _)
theorem returned_columns (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx] sndT (run a N M x) ≐ columnFirst a N M x :=
  (congrSnd (program_at a N M x)).eqTrans (snd_pair _ _)
theorem returned_interchange (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx] fstT (run a N M x) ≐ sndT (run a N M x) :=
  (returned_rows a N M x).eqTrans ((fubini a N M x).eqTrans (returned_columns a N M x).eqSymm)
theorem returned_rows_canonical (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx] canonical (fstT (run a N M x)) :=
  GaussianRationalHorner.canonical_congr (returned_rows a N M x) (row_first_canonical a N M x)
theorem returned_columns_canonical (a : PTm 3) (N M x : PTm n) : Γ ⊢[PRAAx] canonical (sndT (run a N M x)) :=
  GaussianRationalHorner.canonical_congr (returned_columns a N M x) (column_first_canonical a N M x)

theorem fubini_closed (a : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rowFirst a (var 0) (var 1) (var 2) ≐ columnFirst a (var 0) (var 1) (var 2)) := closeUniv 3 (fubini _ _ _ _)
theorem row_recurrence_closed (a : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rowFirst a (succ (var 0)) (var 1) (var 2) ≐
      qadd (rowFirst a (var 0) (var 1) (var 2)) (row a (var 0) (var 1) (var 2))) := closeUniv 3 (row_first_succ _ _ _ _)
theorem column_recurrence_closed (a : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (columnFirst a (var 0) (succ (var 1)) (var 2) ≐
      qadd (columnFirst a (var 0) (var 1) (var 2)) (column a (var 1) (var 0) (var 2))) := closeUniv 3 (column_first_succ _ _ _ _)
theorem empty_dimensions_closed (a : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((rowFirst a zero (var 0) (var 1) ≐ qzero) ⋏
      ((columnFirst a zero (var 0) (var 1) ≐ qzero) ⋏
        ((rowFirst a (var 0) zero (var 1) ≐ qzero) ⋏ columnFirst a (var 0) zero (var 1) ≐ qzero))) :=
  closeUniv 2 (.andI (row_first_zero_rows _ _ _) (.andI (column_first_zero_rows _ _ _)
    (.andI (row_first_zero_columns _ _ _) (column_first_zero_columns _ _ _))))
theorem actual_program_closed (a : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run a (var 0) (var 1) (var 2) ≐ output a (var 0) (var 1) (var 2)) ⋏
      ((fstT (run a (var 0) (var 1) (var 2)) ≐ rowFirst a (var 0) (var 1) (var 2)) ⋏
        sndT (run a (var 0) (var 1) (var 2)) ≐ columnFirst a (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (program_at _ _ _ _) (.andI (returned_rows _ _ _ _) (returned_columns _ _ _ _)))
theorem returned_interchange_closed (a : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (run a (var 0) (var 1) (var 2)) ≐ sndT (run a (var 0) (var 1) (var 2))) ⋏
      (canonical (fstT (run a (var 0) (var 1) (var 2))) ⋏ canonical (sndT (run a (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.andI (returned_interchange _ _ _ _) (.andI (returned_rows_canonical _ _ _ _) (returned_columns_canonical _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianRationalFubini
