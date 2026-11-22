import IPRADerivations.Foundations.RuntimePermutationDigitSum

/-!
# Actual natural finite sums reindexed by numerical permutation words

The existing arbitrary-body adjacent-sum identity is applied to an actual
digit reader. The SAME sorting program preserves this observable and its
proved final identity gives numerical reindexing. No sorting, sum or codec
recursor is introduced here. The fixed body is external syntax; all sizes,
original word codes, persistent data and trace counters are numerical.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RuntimePermutationSums

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RuntimePermutationWords (digit horizon permutationBit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (m w x : PTm n) : PTm n := pairT (RuntimePermutationWords.data m w) x
def read (f : PTm 2) (m w x i : PTm n) : PTm n := inst2 f (digit m w i) x
def reader (f : PTm 2) : PTm 2 := read f (sndT (fstT (var 1))) (fstT (fstT (var 1))) (sndT (var 1)) (var 0)
def total (f : PTm 2) (m w x : PTm n) : PTm n := ap2 (sumF (reader f)) m (data m w x)
def ordinary (f : PTm 2) (m x : PTm n) : PTm n := ap2 (sumF f) m x
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (m w x : PTm n) :
    Syn.subst σ (data m w x) = data (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_read {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (m w x i : PTm n) :
    Syn.subst σ (read f m w x i) = read f (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ x) (Syn.subst σ i) := by simp [read]
@[simp] theorem subst_total {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (m w x : PTm n) :
    Syn.subst σ (total f m w x) = total f (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ x) := by simp [total]
@[simp] theorem subst_ordinary {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (m x : PTm n) :
    Syn.subst σ (ordinary f m x) = ordinary f (Syn.subst σ m) (Syn.subst σ x) := by simp [ordinary]

theorem read_congr (f : PTm 2) {m m' w w' x x' i i' : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ m') (hw : Γ ⊢[PRAAx] w ≐ w') (hx : Γ ⊢[PRAAx] x ≐ x') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    read f m w x i ≐ read f m' w' x' i' := congrInst2 f (RuntimeAdjacentPermutationSwap.digit_congr hm hw hi) hx
theorem reader_at (f : PTm 2) (m w x i : PTm n) : Γ ⊢[PRAAx]
    inst2 (reader f) i (data m w x) ≐ read f m w x i := by
  simp only [reader,inst2,subst_read,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact read_congr f ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _))
    ((congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)) (snd_pair _ _) (.eqRefl _)
theorem total_congr (f : PTm 2) {m m' w w' x x' : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ m') (hw : Γ ⊢[PRAAx] w ≐ w') (hx : Γ ⊢[PRAAx] x ≐ x') : Γ ⊢[PRAAx]
    total f m w x ≐ total f m' w' x' := congrAp2 _ hm (congrPairT (congrPairT hw hm) hx)

theorem adjacent_total (f : PTm 2) (m w j x : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    total f m (RuntimeAdjacentPermutationSwap.swapWord m w j) x ≐ total f m w x := by
  refine (sum_congr_bounded (reader f) (RuntimeAdjacentPermutationSwap.sumSwapBody (reader f))
    (data m (RuntimeAdjacentPermutationSwap.swapWord m w j) x) (pairT j (data m w x)) m ?_).eqTrans
      (RuntimeAdjacentPermutationSwap.adjacent_sum _ _ _ _ hj)
  have hjs : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have low := reader_at (Γ := Δ) f (Syn.shift m)
    (RuntimeAdjacentPermutationSwap.swapWord (Syn.shift m) (Syn.shift w) (Syn.shift j)) (Syn.shift x) (var 0)
  have swapped := congrInst2 (Γ := Δ) f
    (RuntimeAdjacentPermutationSwap.swapped_digit (Syn.shift m) (Syn.shift w) (Syn.shift j) (var 0) hjs.wk Prf.hyp0) (.eqRefl (Syn.shift x))
  have upper := (RuntimeAdjacentPermutationSwap.sum_swap_body_at (Γ := Δ) (reader f) (Syn.shift j) (var 0)
    (data (Syn.shift m) (Syn.shift w) (Syn.shift x))).eqTrans
      (reader_at _ _ _ _ (RuntimeAdjacentPermutationSwap.tau (Syn.shift j) (var 0)))
  simpa only [Δ,Syn.shift,subst_data,subst_pairT,RuntimeAdjacentPermutationSwap.subst_swapWord] using
    low.eqTrans (swapped.eqTrans upper.eqSymm)

theorem step_total (f : PTm 2) (m w x : PTm n) : Γ ⊢[PRAAx]
    total f m (RuntimeWordSorting.sortStep m w) x ≐ total f m w x := by
  refine .orE (RuntimeWordSorting.active_cases m w) ?_ ?_
  · exact total_congr f (.eqRefl _) (RuntimeWordSorting.step_inactive _ _
      (RuntimeWordSorting.inactive_of_active_zero _ _ Prf.hyp0)) (.eqRefl _)
  · exact (total_congr f (.eqRefl _) (RuntimeWordSorting.step_active _ _ Prf.hyp0) (.eqRefl _)).eqTrans
      (adjacent_total _ _ _ _ _ (.andE₁ (RuntimeWordSorting.descent_found _ _ Prf.hyp0)))

/-- One new observable equation along the SAME already constructed trace.
No range/checker guard or incoming trace invariant is assumed here. -/
theorem sorting_total (f : PTm 2) (m w x t : PTm n) : Γ ⊢[PRAAx]
    total f m (RuntimeWordSorting.state m w t) x ≐ total f m w x := by
  have all : Γ ⊢[PRAAx] .all (total f (Syn.shift m)
      (RuntimeWordSorting.state (Syn.shift m) (Syn.shift w) (var 0)) (Syn.shift x) ≐
        total f (Syn.shift m) (Syn.shift w) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_total,RuntimeWordSorting.subst_state,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact total_congr f (.eqRefl _) (RuntimeWordSorting.state_zero _ _) (.eqRefl _)
    · simp only [Fm.subst_eq,subst_total,RuntimeWordSorting.subst_state,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (total_congr f (.eqRefl _) (RuntimeWordSorting.state_succ _ _ _) (.eqRefl _)).eqTrans
        ((step_total _ _ _ _).eqTrans Prf.hyp0)
  simpa only [Fm.subst_eq,subst_total,RuntimeWordSorting.subst_state,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
theorem identity_total (f : PTm 2) (m x : PTm n) : Γ ⊢[PRAAx]
    total f m (RuntimeWordSorting.identityCode m) x ≐ ordinary f m x := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have low := reader_at (Γ := Δ) f (Syn.shift m) (RuntimeWordSorting.identityCode (Syn.shift m)) (Syn.shift x) (var 0)
  have identity := congrInst2 (Γ := Δ) f (RuntimeWordSorting.identity_code_digit (Syn.shift m) (var 0) Prf.hyp0) (.eqRefl (Syn.shift x))
  simpa only [Δ,Syn.shift,subst_data,RuntimeWordSorting.subst_identityCode] using low.eqTrans identity
theorem permutation_sum (f : PTm 2) (m w x : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon m))
    (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one) : Γ ⊢[PRAAx] total f m w x ≐ ordinary f m x :=
  (sorting_total f m w x (RuntimeWordSorting.fuel m)).eqSymm.eqTrans
    ((total_congr f (.eqRefl _) (RuntimeWordSorting.permutation_final_identity _ _ hw hp) (.eqRefl _)).eqTrans
      (identity_total f m x))

theorem empty_total (f : PTm 2) (w x : PTm n) : Γ ⊢[PRAAx] total f zero w x ≐ zero := sum_zero _ _
theorem empty_ordinary (f : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] ordinary f zero x ≐ zero := sum_zero _ _
theorem digit_specialization (m w x : PTm n) : Γ ⊢[PRAAx]
    total (var 0 : PTm 2) m w x ≐ RuntimePermutationDigitSum.digitTotal m w := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have low := reader_at (Γ := Δ) (var 0 : PTm 2) (Syn.shift m) (Syn.shift w) (Syn.shift x) (var 0)
  have high := RuntimePermutationWords.digit_body_at (Γ := Δ) (Syn.shift m) (Syn.shift w) (var 0)
  simpa only [Δ,Syn.shift,subst_data,RuntimePermutationWords.subst_data,read,inst2,Syn.subst_var,
    Matrix.cons_val_zero] using low.eqTrans high.eqSymm

/-! Actual program schemas have only the body syntax fixed externally.
Every numerical bound, original word and persistent datum remains an input. -/
def output (f : PTm 2) (m w x : PTm n) : PTm n := pairT (total f m w x) (ordinary f m x)
def outputF (f : PTm 2) : PR 3 := PTm.toPR (output f (var 0) (var 1) (var 2))
def run (f : PTm 2) (m w x : PTm n) : PTm n := ap3 (outputF f) m w x
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (m w x : PTm n) :
    Syn.subst σ (output f m w x) = output f (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (f : PTm 2) (m w x : PTm n) :
    Syn.subst σ (run f m w x) = run f (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ x) := by simp [run]
theorem program_at (f : PTm 2) (m w x : PTm n) : Γ ⊢[PRAAx] run f m w x ≐ output f m w x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output f (var 0) (var 1) (var 2) : PTm 3) ![m,w,x]
theorem returned_total (f : PTm 2) (m w x : PTm n) : Γ ⊢[PRAAx] fstT (run f m w x) ≐ total f m w x :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_ordinary (f : PTm 2) (m w x : PTm n) : Γ ⊢[PRAAx] sndT (run f m w x) ≐ ordinary f m x :=
  (congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_equality (f : PTm 2) (m w x : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon m))
    (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one) : Γ ⊢[PRAAx] fstT (run f m w x) ≐ sndT (run f m w x) :=
  (returned_total _ _ _ _).eqTrans ((permutation_sum _ _ _ _ hw hp).eqTrans (returned_ordinary _ _ _ _).eqSymm)

theorem actual_adjacent_total_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (succ (var 2)) (var 0) ⟶ total f (var 0) (RuntimeAdjacentPermutationSwap.swapWord (var 0) (var 1) (var 2)) (var 3) ≐
      total f (var 0) (var 1) (var 3)) := closeUniv 4 (.impI (adjacent_total _ _ _ _ _ Prf.hyp0))
theorem actual_sorting_observable_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (total f (var 0) (RuntimeWordSorting.state (var 0) (var 1) (var 3)) (var 2) ≐ total f (var 0) (var 1) (var 2)) :=
  closeUniv 4 (sorting_total _ _ _ _ _)
theorem actual_identity_total_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (total f (var 0) (RuntimeWordSorting.identityCode (var 0)) (var 1) ≐ ordinary f (var 0) (var 1)) :=
  closeUniv 2 (identity_total _ _ _)
theorem actual_permutation_sum_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (horizon (var 0)) ⟶ permutationBit (var 0) (var 1) ≐ one ⟶
      total f (var 0) (var 1) (var 2) ≐ ordinary f (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (permutation_sum _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_empty_totals_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((total f zero (var 0) (var 1) ≐ zero) ⋏ (ordinary f zero (var 1) ≐ zero)) :=
  closeUniv 2 (.andI (empty_total _ _ _) (empty_ordinary _ _))
theorem actual_digit_specialization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (total (var 0 : PTm 2) (var 0) (var 1) (var 2) ≐ RuntimePermutationDigitSum.digitTotal (var 0) (var 1)) :=
  closeUniv 3 (digit_specialization _ _ _)
theorem actual_sum_program_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run f (var 0) (var 1) (var 2) ≐ output f (var 0) (var 1) (var 2)) ⋏
      ((fstT (run f (var 0) (var 1) (var 2)) ≐ total f (var 0) (var 1) (var 2)) ⋏
        (sndT (run f (var 0) (var 1) (var 2)) ≐ ordinary f (var 0) (var 2)))) :=
  closeUniv 3 (.andI (program_at _ _ _ _) (.andI (returned_total _ _ _ _) (returned_ordinary _ _ _ _)))
theorem actual_returned_sum_equality_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (horizon (var 0)) ⟶ permutationBit (var 0) (var 1) ≐ one ⟶
      fstT (run f (var 0) (var 1) (var 2)) ≐ sndT (run f (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (returned_equality _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.RuntimePermutationSums
