import IPRADerivations.Analysis.Polynomials.Elimination.GaussianRationalEliminationLoop
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalRowSpanPivotTransfer
import IPRADerivations.Core.CongruenceTactic

/-!
# Backward transport of coefficients through rectangular elimination

The numerical recursion revisits the actual column prefixes in reverse
order. A skipped column leaves the weights unchanged. A successful pivot
uses the coefficient transfer for that exact step. Each coordinate of the
represented vector stays fixed throughout the recursion.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRowSpanRewind

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalEliminationLoop (matrix history matrix_zero matrix_succ)
open GaussianRationalPivotSearch (flag selected flag_cases next_failure next_success selected_correct)
open GaussianRationalRowSpan (columnBody columnData combinationAt combination_lookup membership membership_at)
open GaussianRationalRowSpanPivotTransfer (transfer transfer_length)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_zero sel_one)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def backward (A R N p u : PTm n) : PTm n :=
  let E := matrix A R N p
  let H := history A R N p
  sel (flag E R H p p) (transfer E R u (selected E R H p p) p) u

def data (A R N c u : PTm n) : PTm n := pairT u (pairT c (pairT A (pairT R N)))
def baseBody : PTm 1 := fstT (var 0)
def stepBody : PTm 3 := backward (fstT (sndT (sndT (var 2))))
  (fstT (sndT (sndT (sndT (var 2))))) (sndT (sndT (sndT (sndT (var 2)))))
  (monus (fstT (sndT (var 2))) (succ (var 0))) (var 1)
def rewindF : PR 2 := rec2 baseBody stepBody
def rewind (A R N c u t : PTm n) : PTm n := ap2 rewindF t (data A R N c u)

@[simp] theorem subst_backward {k : ℕ} (σ : Fin n → PTm k) (A R N p u : PTm n) :
    Syn.subst σ (backward A R N p u) = backward (Syn.subst σ A) (Syn.subst σ R)
      (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ u) := by simp [backward,sel]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (A R N c u : PTm n) :
    Syn.subst σ (data A R N c u) = data (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ c) (Syn.subst σ u) := by simp [data]
@[simp] theorem subst_rewind {k : ℕ} (σ : Fin n → PTm k) (A R N c u t : PTm n) :
    Syn.subst σ (rewind A R N c u t) = rewind (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ c) (Syn.subst σ u) (Syn.subst σ t) := by simp [rewind]

theorem backward_congr {A A' R R' N N' p p' u u' : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A')
    (hR : Γ ⊢[PRAAx] R ≐ R') (hN : Γ ⊢[PRAAx] N ≐ N') (hp : Γ ⊢[PRAAx] p ≐ p')
    (hu : Γ ⊢[PRAAx] u ≐ u') : Γ ⊢[PRAAx] backward A R N p u ≐ backward A' R' N' p' u' := by
  ipra_congr (backward (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hA, hR, hN, hp, hu]

theorem rewind_zero (A R N c u : PTm n) : Γ ⊢[PRAAx] rewind A R N c u zero ≐ u := by
  have e := rec2_zero (Γ := Γ) baseBody stepBody (data A R N c u)
  simp only [baseBody,subst_fstT,Syn.subst_var] at e
  exact e.eqTrans (fst_pair _ _)

theorem rewind_succ (A R N c u t : PTm n) : Γ ⊢[PRAAx]
    rewind A R N c u (succ t) ≐ backward A R N (monus c (succ t)) (rewind A R N c u t) := by
  have e := rec2_succ (Γ := Γ) baseBody stepBody t (data A R N c u)
  simp only [stepBody,subst_backward,subst_fstT,subst_sndT,PTm.subst_monus,ConciseIPRA.PTm.subst_succ,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at e
  have tail := snd_pair (Γ := Γ) u (pairT c (pairT A (pairT R N)))
  have rest := (congrSnd tail).eqTrans (snd_pair c (pairT A (pairT R N)))
  have dims := (congrSnd rest).eqTrans (snd_pair A (pairT R N))
  exact e.eqTrans (backward_congr ((congrFst rest).eqTrans (fst_pair _ _))
    ((congrFst dims).eqTrans (fst_pair _ _)) ((congrSnd dims).eqTrans (snd_pair _ _))
    (congrMonus ((congrFst tail).eqTrans (fst_pair _ _)) (.eqRefl _)) (.eqRefl _))

theorem backward_length (A R N p u : PTm n) (hu : Γ ⊢[PRAAx] length u ≐ R) :
    Γ ⊢[PRAAx] length (backward A R N p u) ≐ R := by
  let E := matrix A R N p
  let H := history A R N p
  refine .orE (flag_cases E R H p p) ?_ ?_
  · exact (congrFst (sel_zero Prf.hyp0)).eqTrans hu.wk
  · exact (congrFst (sel_one Prf.hyp0)).eqTrans (transfer_length E R u (selected E R H p p) p)

theorem rewind_length (A R N c u t : PTm n) (hu : Γ ⊢[PRAAx] length u ≐ R) :
    Γ ⊢[PRAAx] length (rewind A R N c u t) ≐ R := by
  have all : Γ ⊢[PRAAx] .all (length (rewind (Syn.shift A) (Syn.shift R) (Syn.shift N)
      (Syn.shift c) (Syn.shift u) (var 0)) ≐ Syn.shift R) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_length,subst_rewind,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (congrFst (rewind_zero _ _ _ _ _)).eqTrans hu
    · simp only [Fm.subst_eq,subst_length,subst_rewind,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (congrFst (rewind_succ _ _ _ _ _ _)).eqTrans (backward_length _ _ _ _ _ Prf.hyp0)
  simpa only [Fm.subst_eq,subst_length,subst_rewind,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t

theorem combination_congr {A B R u w j : PTm n} (hA : Γ ⊢[PRAAx] A ≐ B) (hu : Γ ⊢[PRAAx] u ≐ w) :
    Γ ⊢[PRAAx] combinationAt A R u j ≐ combinationAt B R w j :=
  GaussianRationalFiniteSum.sum_index_congr columnBody (.eqRefl R) (congrPairT hA (congrPairT hu (.eqRefl j)))

private theorem matrix_index_congr (A R N : PTm n) {p q : PTm n} (h : Γ ⊢[PRAAx] p ≐ q) :
    Γ ⊢[PRAAx] matrix A R N p ≐ matrix A R N q :=
  congrFst (congrAp2 GaussianRationalEliminationLoop.stateF h (.eqRefl _))

theorem backward_column (A R N p u j : PTm n)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    combinationAt (matrix A R N p) R (backward A R N p u) j ≐ combinationAt (matrix A R N (succ p)) R u j := by
  let E := matrix A R N p
  let H := history A R N p
  have step := matrix_succ (Γ := Γ) A R N p
  refine .orE (flag_cases E R H p p) ?_ ?_
  · have stayed := step.wk.eqTrans (next_failure E R N H p p Prf.hyp0)
    exact (combination_congr (.eqRefl E) (sel_zero Prf.hyp0)).eqTrans
      (combination_congr stayed.eqSymm (.eqRefl u))
  · have selectedFacts := selected_correct (Γ := (flag E R H p p ≐ one) :: Γ) E R H p p Prf.hyp0
    have changed := step.wk.eqTrans (next_success E R N H p p Prf.hyp0)
    exact (combination_congr (.eqRefl E) (sel_one Prf.hyp0)).eqTrans
      ((GaussianRationalRowSpanPivotTransfer.column_backward E R N u (selected E R H p p) p j
        (.andE₁ selectedFacts) hj.wk).eqTrans (combination_congr changed.eqSymm (.eqRefl u)))

theorem previous_prefix (c t : PTm n) (h : Γ ⊢[PRAAx] le (succ t) c) :
    Γ ⊢[PRAAx] monus c t ≐ succ (monus c (succ t)) := by
  let p := monus c (succ t)
  have reordered : Γ ⊢[PRAAx] succ t + p ≐ succ p + t := by ipra_ring
  exact (congrMonus ((eq_add_of_le h).eqTrans reordered) (.eqRefl t)).eqTrans (add_monus _ _)

def columnLaw (A R N c u j t : PTm n) : Fm PTm n := le t c ⟶
  combinationAt (matrix A R N (monus c t)) R (rewind A R N c u t) j ≐ combinationAt (matrix A R N c) R u j

@[simp] theorem subst_columnLaw {k : ℕ} (σ : Fin n → PTm k) (A R N c u j t : PTm n) :
    (columnLaw A R N c u j t).subst σ = columnLaw (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N)
      (Syn.subst σ c) (Syn.subst σ u) (Syn.subst σ j) (Syn.subst σ t) := by simp [columnLaw]

theorem column_succ (A R N c u j t : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (ht : Γ ⊢[PRAAx] le (succ t) c) (h : Γ ⊢[PRAAx] columnLaw A R N c u j t) : Γ ⊢[PRAAx]
    combinationAt (matrix A R N (monus c (succ t))) R (rewind A R N c u (succ t)) j ≐
      combinationAt (matrix A R N c) R u j := by
  let p := monus c (succ t)
  let w := rewind A R N c u t
  have older := previous_prefix c t ht
  have prev := matrix_index_congr A R N older.eqSymm
  exact (combination_congr (.eqRefl _) (rewind_succ A R N c u t)).eqTrans
    ((backward_column A R N p w j hj).eqTrans ((combination_congr prev (.eqRefl w)).eqTrans
      (.impE h (le_trans (le_succ_self _) ht))))

theorem rewind_column (A R N c u j t : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (ht : Γ ⊢[PRAAx] le t c) : Γ ⊢[PRAAx]
    combinationAt (matrix A R N (monus c t)) R (rewind A R N c u t) j ≐ combinationAt (matrix A R N c) R u j := by
  have hjs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hj.shift
  have all : Γ ⊢[PRAAx] .all (columnLaw (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c)
      (Syn.shift u) (Syn.shift j) (var 0)) := by
    refine PRA.qfInd _ (by simp [columnLaw,Fm.QF,le]) ?_ ?_
    · simp only [subst_columnLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (combination_congr
        (matrix_index_congr A R N (monus_zero c))
        (rewind_zero _ _ _ _ _))
    · simp only [subst_columnLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (column_succ (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c) (Syn.shift u)
        (Syn.shift j) (var 0) hjs.wk.wk Prf.hyp0 Prf.hyp1)
  have atT : Γ ⊢[PRAAx] columnLaw A R N c u j t := by
    simpa only [subst_columnLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE t
  exact .impE atT ht

def originalWeights (A R N c u : PTm n) : PTm n := rewind A R N c u c

@[simp] theorem subst_originalWeights {k : ℕ} (σ : Fin n → PTm k) (A R N c u : PTm n) :
    Syn.subst σ (originalWeights A R N c u) = originalWeights (Syn.subst σ A) (Syn.subst σ R)
      (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ u) := by simp [originalWeights]

theorem original_column (A R N c u j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] combinationAt A R (originalWeights A R N c u) j ≐ combinationAt (matrix A R N c) R u j := by
  have base := (matrix_index_congr (Γ := Γ) A R N (monus_self c)).eqTrans
    (matrix_zero A R N)
  exact (combination_congr base.eqSymm (.eqRefl _)).eqTrans (rewind_column A R N c u j c hj (le_refl c))

theorem membership_original (A R N c u v : PTm n)
    (h : Γ ⊢[PRAAx] membership (matrix A R N c) R N u v) :
    Γ ⊢[PRAAx] membership A R N (originalWeights A R N c u) v := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] membership (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c))
      (Syn.shift R) (Syn.shift N) (Syn.shift u) (Syn.shift v) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have left := combination_lookup (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N)
    (originalWeights (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c) (Syn.shift u)) (var 0) Prf.hyp0
  have right := combination_lookup (Γ := Δ) (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift c))
    (Syn.shift R) (Syn.shift N) (Syn.shift u) (var 0) Prf.hyp0
  have eq := left.eqTrans ((original_column _ _ _ _ _ _ Prf.hyp0).eqTrans right.eqSymm)
  have value := GaussianRationalValueEquality.equal_values_of_recode_equal _ _
    (GaussianTranslatedNonconstant.recode_congr eq.eqSymm)
  simpa [Δ,Syn.shift] using GaussianRationalValueEquality.value_equal_trans _ _ _
    (membership_at _ _ _ _ _ _ hs.wk Prf.hyp0) value

theorem actual_rewind_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (length (var 4) ≐ var 1 ⟶ length (rewind (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ var 1) :=
  closeUniv 6 (.impI (rewind_length _ _ _ _ _ _ Prf.hyp0))

theorem actual_rewind_column_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (lt (var 5) (var 2) ⟶ le (var 6) (var 3) ⟶
      combinationAt (matrix (var 0) (var 1) (var 2) (monus (var 3) (var 6))) (var 1)
        (rewind (var 0) (var 1) (var 2) (var 3) (var 4) (var 6)) (var 5) ≐
      combinationAt (matrix (var 0) (var 1) (var 2) (var 3)) (var 1) (var 4) (var 5)) :=
  closeUniv 7 (.impI (.impI (rewind_column _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_membership_original_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (membership (matrix (var 0) (var 1) (var 2) (var 3)) (var 1) (var 2) (var 4) (var 5) ⟶
      membership (var 0) (var 1) (var 2) (originalWeights (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (membership_original _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalRowSpanRewind
