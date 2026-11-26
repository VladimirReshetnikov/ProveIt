import IPRADerivations.Foundations.RuntimePermutationWords
import IPRADerivations.Foundations.GuardedTotalization
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.ParityArith
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# Actual adjacent position swaps of numeric permutation words

Dimensions, words, swap positions and retained indices are numerical.
The mixed-radix horizon guard is kept separate from the bounded tuple test.
Natural finite-sum conservation proves the actual inversion-parity change;
no incoming sign, swapped-permutation or global reindexing law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RuntimeAdjacentPermutationSwap

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_zero sel_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def tau (j i : PTm n) : PTm n := sel (eqb i j) (succ j) (sel (eqb i (succ j)) j i)
def tupleData (P j : PTm n) : PTm n := pairT P j
def tupleBody : PTm 2 := entry (fstT (var 1)) (tau (sndT (var 1)) (var 0))
def swapTuple (P m j : PTm n) : PTm n := sequence tupleBody m (tupleData P j)
def swapWord (m w j : PTm n) : PTm n := RuntimePermutationWords.encode
  (swapTuple (RuntimePermutationWords.word m w) m j) m
def rankSwap (m j t : PTm n) : PTm n := RuntimePermutationWords.position
  (swapTuple (RuntimePermutationWords.word m (entry (RuntimePermutationWords.words m) t)) m j) m

ipra_subst tau [sel]
ipra_subst tupleData
ipra_subst swapTuple
ipra_subst swapWord
ipra_subst rankSwap

alias different_of_lt := Common.ne_of_lt
theorem different_symm {a b : PTm n} (h : Γ ⊢[PRAAx] neg (a ≐ b)) : Γ ⊢[PRAAx] neg (b ≐ a) :=
  .impI (.impE h.wk Prf.hyp0.eqSymm)
theorem tau_congr {j j' i i' : PTm n} (hj : Γ ⊢[PRAAx] j ≐ j') (hi : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] tau j i ≐ tau j' i' := by
  ipra_congr (tau (var 0) (var 1) : PTm 2) with [hj, hi]
theorem tau_left (j : PTm n) : Γ ⊢[PRAAx] tau j j ≐ succ j := sel_one (eqb_of_eq (.eqRefl _))
theorem tau_right (j : PTm n) : Γ ⊢[PRAAx] tau j (succ j) ≐ j :=
  (sel_zero (eqb_of_ne (different_symm (different_of_lt (le_refl (succ j)))))).eqTrans
    (sel_one (eqb_of_eq (.eqRefl _)))
theorem tau_other (j i : PTm n) (h0 : Γ ⊢[PRAAx] neg (i ≐ j)) (h1 : Γ ⊢[PRAAx] neg (i ≐ succ j)) :
    Γ ⊢[PRAAx] tau j i ≐ i := (sel_zero (eqb_of_ne h0)).eqTrans (sel_zero (eqb_of_ne h1))
theorem tau_involution (j i : PTm n) : Γ ⊢[PRAAx] tau j (tau j i) ≐ i := by
  refine .orE (eq_or_ne i j) ?_ ?_
  · exact (tau_congr (.eqRefl _) ((tau_congr (.eqRefl _) Prf.hyp0).eqTrans (tau_left _))).eqTrans
      ((tau_right _).eqTrans Prf.hyp0.eqSymm)
  · refine .orE (eq_or_ne i (succ j)) ?_ ?_
    · exact (tau_congr (.eqRefl _) ((tau_congr (.eqRefl _) Prf.hyp0).eqTrans (tau_right _))).eqTrans
        ((tau_left _).eqTrans Prf.hyp0.eqSymm)
    · exact (tau_congr (.eqRefl _) (tau_other _ _ Prf.hyp1 Prf.hyp0)).eqTrans (tau_other _ _ Prf.hyp1 Prf.hyp0)
theorem tau_range (m j i : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) (hi : Γ ⊢[PRAAx] lt i m) :
    Γ ⊢[PRAAx] lt (tau j i) m := by
  refine .orE (eq_or_ne i j) ?_ ?_
  · exact lt_congr ((tau_congr (.eqRefl _) Prf.hyp0).eqTrans (tau_left _)).eqSymm (.eqRefl _) hj.wk
  · refine .orE (eq_or_ne i (succ j)) ?_ ?_
    · exact lt_congr ((tau_congr (.eqRefl _) Prf.hyp0).eqTrans (tau_right _)).eqSymm (.eqRefl _)
        (lt_of_le_of_lt (le_succ_self _) hj.wk.wk)
    · exact lt_congr (tau_other _ _ Prf.hyp1 Prf.hyp0).eqSymm (.eqRefl _) hi.wk.wk

theorem tuple_body_at (P j i : PTm n) : Γ ⊢[PRAAx] inst2 tupleBody i (tupleData P j) ≐ entry P (tau j i) := by
  simpa only [tupleBody,inst2,subst_entry,subst_tau,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,tupleData] using
    entry_congr (fst_pair P j) (tau_congr (snd_pair P j) (.eqRefl i))
theorem tuple_length (P m j : PTm n) : Γ ⊢[PRAAx] length (swapTuple P m j) ≐ m := sequence_length _ _ _
theorem tuple_lookup (P m j i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    entry (swapTuple P m j) i ≐ entry P (tau j i) :=
  (sequence_decode tupleBody hi).eqTrans (tuple_body_at _ _ _)
theorem tuple_range (P m j : PTm n) (hP : Γ ⊢[PRAAx] RuntimePermutationWords.range P m)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx] RuntimePermutationWords.range (swapTuple P m j) m := by
  refine .allI (.impI ?_)
  have ps : Γ.map Fm.shift ⊢[PRAAx] RuntimePermutationWords.range (Syn.shift P) (Syn.shift m) := by
    simpa only [Fm.shift,RuntimePermutationWords.subst_range,Syn.shift] using hP.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  simpa only [Syn.shift,subst_swapTuple] using lt_congr (tuple_lookup _ _ _ _ Prf.hyp0).eqSymm (.eqRefl _)
    (RuntimePermutationWords.range_at _ _ _ ps.wk (tau_range _ _ _ js.wk Prf.hyp0))
theorem distinct_entries (P m i l : PTm n) (h : Γ ⊢[PRAAx] RuntimePermutationWords.distinct P m)
    (hi : Γ ⊢[PRAAx] lt i m) (hl : Γ ⊢[PRAAx] lt l m) (hne : Γ ⊢[PRAAx] neg (i ≐ l)) :
    Γ ⊢[PRAAx] neg (entry P i ≐ entry P l) := by
  refine .orE (lt_or_le i l) ?_ ?_
  · exact different_symm (RuntimePermutationWords.distinct_at _ _ _ _ h.wk hl.wk Prf.hyp0)
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · exact RuntimePermutationWords.distinct_at _ _ _ _ h.wk.wk hi.wk.wk Prf.hyp0
    · exact .botE _ (.impE hne.wk.wk Prf.hyp0.eqSymm)

theorem tuple_preserved (P m j : PTm n) (hP : Γ ⊢[PRAAx] RuntimePermutationWords.tuple P m)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx] RuntimePermutationWords.tuple (swapTuple P m j) m := by
  refine .andI (tuple_length _ _ _) (.andI (tuple_range _ _ _ (.andE₁ (.andE₂ hP)) hj) ?_)
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (var 1) :: (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift).map Fm.shift
  have ps : Δ ⊢[PRAAx] RuntimePermutationWords.tuple (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,List.map_cons,Fm.shift,RuntimePermutationWords.subst_tuple,Syn.shift] using hP.shift.wk.shift.wk
  have js0 : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  have js1 : lt (var 0) (Syn.shift m) :: Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := js0.wk
  have js : Δ ⊢[PRAAx] lt (succ (Syn.shift (Syn.shift j))) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using js1.shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.subst_var,Syn.shift,Fin.succ_zero_eq_one] using
      (Prf.hyp1 : Δ ⊢[PRAAx] Fm.shift (lt (var 0) (Syn.shift m)))
  have hl : Δ ⊢[PRAAx] lt (var 0) (var 1) := Prf.hyp0
  have hne : Δ ⊢[PRAAx] neg (tau (Syn.shift (Syn.shift j)) (var 1) ≐ tau (Syn.shift (Syn.shift j)) (var 0)) := by
    refine .impI ?_
    exact .impE (different_of_lt hl).wk
      ((tau_involution _ _).wk.eqSymm.eqTrans ((tau_congr (.eqRefl _) Prf.hyp0).eqTrans (tau_involution _ _))).eqSymm
  have no := distinct_entries _ _ _ _ (.andE₂ (.andE₂ ps)) (tau_range _ _ _ js hi)
    (tau_range _ _ _ js (lt_of_lt_of_le hl (le_of_lt hi))) hne
  have ei := tuple_lookup (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift j)) (var 1) hi
  have el := tuple_lookup (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift j)) (var 0)
    (lt_of_lt_of_le hl (le_of_lt hi))
  have out : Δ ⊢[PRAAx] neg (entry (swapTuple (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift j))) (var 1) ≐
      entry (swapTuple (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift j))) (var 0)) :=
    .impI (.impE no.wk (ei.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans el.wk)))
  simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.subst_var,Syn.shift,Fin.succ_zero_eq_one,subst_swapTuple] using out

theorem word_range (m w : PTm n) : Γ ⊢[PRAAx] RuntimePermutationWords.range (RuntimePermutationWords.word m w) m := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,RuntimePermutationWords.subst_word] using lt_congr
    (RuntimePermutationWords.word_lookup _ _ _ Prf.hyp0).eqSymm (.eqRefl _)
    (RuntimePermutationWords.digit_bound (Syn.shift m) (Syn.shift w) (var 0) Prf.hyp0)
theorem swapped_bound (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    lt (swapWord m w j) (RuntimePermutationWords.horizon m) :=
  RuntimePermutationWords.encode_bound _ _ (tuple_range _ _ _ (word_range _ _) hj)
theorem swapped_digit (m w j i : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    RuntimePermutationWords.digit m (swapWord m w j) i ≐ RuntimePermutationWords.digit m w (tau j i) :=
  (RuntimePermutationWords.encode_decode _ _ _ (tuple_range _ _ _ (word_range _ _) hj) hi).eqTrans
    ((tuple_lookup _ _ _ _ hi).eqTrans (RuntimePermutationWords.word_lookup _ _ _ (tau_range _ _ _ hj hi)))

theorem digit_congr {m m' w w' i i' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m')
    (hw : Γ ⊢[PRAAx] w ≐ w') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx]
    RuntimePermutationWords.digit m w i ≐ RuntimePermutationWords.digit m' w' i' := by
  ipra_congr (RuntimePermutationWords.digit (var 0) (var 1) (var 2) : PTm 3) with [hm, hw, hi]
theorem swapWord_congr {m m' w w' j j' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m')
    (hw : Γ ⊢[PRAAx] w ≐ w') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    swapWord m w j ≐ swapWord m' w' j' := by
  ipra_congr (swapWord (var 0) (var 1) (var 2) : PTm 3) with [hm, hw, hj]
theorem swapped_permutation (m w j : PTm n) (h : Γ ⊢[PRAAx] RuntimePermutationWords.permutation m w)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx] RuntimePermutationWords.permutation m (swapWord m w j) :=
  RuntimePermutationWords.encoded_tuple _ _ (tuple_preserved _ _ _ h hj)

theorem word_involution (m w j : PTm n) (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx] swapWord m (swapWord m w j) j ≐ w := by
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  apply RuntimePermutationWords.word_unique m (swapWord m (swapWord m w j) j) w (swapped_bound _ _ _ hj) hw
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have e : Δ ⊢[PRAAx]
      entry (RuntimePermutationWords.word (Syn.shift m) (swapWord (Syn.shift m) (swapWord (Syn.shift m) (Syn.shift w) (Syn.shift j)) (Syn.shift j))) (var 0) ≐
        entry (RuntimePermutationWords.word (Syn.shift m) (Syn.shift w)) (var 0) :=
    (RuntimePermutationWords.word_lookup _ _ _ Prf.hyp0).eqTrans
      ((swapped_digit _ _ _ _ js.wk Prf.hyp0).eqTrans
        ((swapped_digit _ _ _ _ js.wk (tau_range _ _ _ js.wk Prf.hyp0)).eqTrans
          ((digit_congr (.eqRefl _) (.eqRefl _) (tau_involution _ _)).eqTrans
            (RuntimePermutationWords.word_lookup _ _ _ Prf.hyp0).eqSymm)))
  simpa only [Δ,Syn.shift,subst_swapWord,RuntimePermutationWords.subst_word] using e

theorem retained_transport (m j t : PTm n) (ht : Γ ⊢[PRAAx] lt t (RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    lt (rankSwap m j t) (RuntimePermutationWords.count m) ⋏
      (entry (RuntimePermutationWords.words m) (rankSwap m j t) ≐
        swapWord m (entry (RuntimePermutationWords.words m) t) j) :=
  RuntimePermutationWords.listed _ _ (tuple_preserved _ _ _ (RuntimePermutationWords.retained_valid _ _ ht) hj)
theorem rank_involution (m j t : PTm n) (ht : Γ ⊢[PRAAx] lt t (RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx] rankSwap m j (rankSwap m j t) ≐ t := by
  have first := retained_transport _ _ _ ht hj
  have next := retained_transport _ _ _ (.andE₁ first) hj
  apply RuntimePermutationWords.retained_position_unique _ _ _ (.andE₁ next) ht
  exact (Prf.andE₂ next).eqTrans
    ((swapWord_congr (.eqRefl _) (Prf.andE₂ first) (.eqRefl _)).eqTrans
      (word_involution _ _ _ (RuntimePermutationWords.retained_bound _ _ ht) hj))

/-! Adjacent finite-sum exchange uses genuine numeric cut points. In
particular no unbounded rangeAll hypothesis is imposed on the raw swap. -/
def sumSwapBody (g : PTm 2) : PTm 2 := inst2 g (tau (fstT (var 1)) (var 0)) (sndT (var 1))
theorem sum_swap_body_at (g : PTm 2) (j i x : PTm n) : Γ ⊢[PRAAx]
    inst2 (sumSwapBody g) i (pairT j x) ≐ inst2 g (tau j i) x := by
  have vector : (fun k => Syn.subst ![i,pairT j x] ((![tau (fstT (var 1)) (var 0),sndT (var 1)] : Fin 2 → PTm 2) k)) =
      ![tau (fstT (pairT j x)) i,sndT (pairT j x)] := by
    funext k
    fin_cases k <;> simp
  simp only [sumSwapBody,inst2,Syn.subst_subst]
  rw [vector]
  exact congrInst2 g (tau_congr (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

theorem off_at (g : PTm 2) (a i x : PTm n) : Γ ⊢[PRAAx]
    inst2 (offB g) i (pairT a x) ≐ inst2 g (a+i) x := by
  rw [inst2_offB]
  exact congrInst2 g (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)
theorem sum_two (g : PTm 2) (x : PTm n) : Γ ⊢[PRAAx]
    ap2 (sumF g) two x ≐ inst2 g zero x+inst2 g one x :=
  (sum_succ' g one x).eqTrans (congrAdd ((sum_succ' g zero x).eqTrans
    ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans (zero_add _))) (.eqRefl _))
theorem tau_before (j i : PTm n) (hi : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx] tau j i ≐ i :=
  tau_other _ _ (different_of_lt hi) (different_of_lt (lt_of_lt_of_le hi (le_succ_self _)))
theorem tau_after (j i : PTm n) (hi : Γ ⊢[PRAAx] le (succ (succ j)) i) : Γ ⊢[PRAAx] tau j i ≐ i :=
  tau_other _ _ (different_symm (different_of_lt (lt_of_le_of_lt (le_succ_self _) hi)))
    (different_symm (different_of_lt hi))

theorem swap_sum_prefix (g : PTm 2) (j x : PTm n) : Γ ⊢[PRAAx]
    ap2 (sumF (sumSwapBody g)) j (pairT j x) ≐ ap2 (sumF g) j x := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_pairT] using
    (sum_swap_body_at g (Syn.shift j) (var 0) (Syn.shift x)).eqTrans
      (congrInst2 g (tau_before _ _ Prf.hyp0) (.eqRefl _))
theorem swap_sum_middle (g : PTm 2) (j x : PTm n) : Γ ⊢[PRAAx]
    ap2 (sumF (offB (sumSwapBody g))) two (pairT j (pairT j x)) ≐
      ap2 (sumF (offB g)) two (pairT j x) := by
  have e0 := (off_at (Γ := Γ) (sumSwapBody g) j zero (pairT j x)).eqTrans
    ((sum_swap_body_at g j (j+zero) x).eqTrans
      (congrInst2 g ((tau_congr (.eqRefl _) (add_zero _)).eqTrans (tau_left _)) (.eqRefl _)))
  have e1 := (off_at (Γ := Γ) (sumSwapBody g) j one (pairT j x)).eqTrans
    ((sum_swap_body_at g j (j+one) x).eqTrans
      (congrInst2 g ((tau_congr (.eqRefl _) (succ_eq_add_one _).eqSymm).eqTrans (tau_right _)) (.eqRefl _)))
  have f0 := (off_at (Γ := Γ) g j zero x).eqTrans (congrInst2 g (add_zero _) (.eqRefl _))
  have f1 := (off_at (Γ := Γ) g j one x).eqTrans (congrInst2 g (succ_eq_add_one _).eqSymm (.eqRefl _))
  refine withEq (sum_two (Γ := Γ) (offB (sumSwapBody g)) (pairT j (pairT j x))) fun a =>
    withEq (sum_two (Γ := Γ) (offB g) (pairT j x)) fun b =>
    withEq e0 fun c => withEq e1 fun d => withEq f0 fun e => withEq f1 fun f => ?_
  apply deriveNat
  ipra_simps
  rw [a,b,c,d,e,f]
  ring

theorem swap_sum_tail (g : PTm 2) (j t x : PTm n) : Γ ⊢[PRAAx]
    ap2 (sumF (offB (sumSwapBody g))) t (pairT (j+two) (pairT j x)) ≐
      ap2 (sumF (offB g)) t (pairT (j+two) x) := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift t) :: Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] le (succ (succ (Syn.shift j))) (Syn.shift j+two+var 0) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_add_right (Syn.shift j+two) (var 0))
  have e := (off_at (Γ := Δ) (sumSwapBody g) (Syn.shift j+two) (var 0) (pairT (Syn.shift j) (Syn.shift x))).eqTrans
    ((sum_swap_body_at g (Syn.shift j) (Syn.shift j+two+var 0) (Syn.shift x)).eqTrans
      ((congrInst2 g (tau_after _ _ h) (.eqRefl _)).eqTrans
        (off_at g (Syn.shift j+two) (var 0) (Syn.shift x)).eqSymm))
  simpa only [Δ,Syn.shift,subst_pairT,PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using e

theorem adjacent_sum (g : PTm 2) (m j x : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    ap2 (sumF (sumSwapBody g)) m (pairT j x) ≐ ap2 (sumF g) m x := by
  let t := monus m (succ (succ j))
  have span : Γ ⊢[PRAAx] m ≐ j+two+t := (eq_add_of_le hj).eqTrans (by ipra_ring)
  exact (congrAp2 (sumF (sumSwapBody g)) span (.eqRefl _)).eqTrans
    ((sum_split₃ _ j two t (pairT j x)).eqTrans
      ((congrAdd (congrAdd (swap_sum_prefix _ _ _) (swap_sum_middle _ _ _)) (swap_sum_tail _ _ _ _)).eqTrans
        ((sum_split₃ g j two t x).eqSymm.eqTrans (congrAp2 (sumF g) span.eqSymm (.eqRefl _)))))

theorem pair_first {a b c d : PTm n} (h : Γ ⊢[PRAAx] pairT a b ≐ pairT c d) : Γ ⊢[PRAAx] a ≐ c :=
  (fst_pair _ _).eqSymm.eqTrans ((congrFst h).eqTrans (fst_pair _ _))
theorem pair_second {a b c d : PTm n} (h : Γ ⊢[PRAAx] pairT a b ≐ pairT c d) : Γ ⊢[PRAAx] b ≐ d :=
  (snd_pair _ _).eqSymm.eqTrans ((congrSnd h).eqTrans (snd_pair _ _))
theorem before_one (j i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ j)) (hne : Γ ⊢[PRAAx] neg (i ≐ j)) :
    Γ ⊢[PRAAx] lt i j := .orE (lt_succ_cases hi) Prf.hyp0 (.botE _ (.impE hne.wk Prf.hyp0))
theorem after_one (j i : PTm n) (hi : Γ ⊢[PRAAx] lt j i) (hne : Γ ⊢[PRAAx] neg (i ≐ succ j)) :
    Γ ⊢[PRAAx] lt (succ j) i := .orE (lt_or_eq_of_le hi) Prf.hyp0 (.botE _ (.impE hne.wk Prf.hyp0.eqSymm))
theorem tau_order_left (j l : PTm n) (hl : Γ ⊢[PRAAx] lt j l) (hne : Γ ⊢[PRAAx] neg (l ≐ succ j)) :
    Γ ⊢[PRAAx] lt (tau j j) (tau j l) :=
  lt_congr (tau_left _).eqSymm (tau_other _ _ (different_symm (different_of_lt hl)) hne).eqSymm (after_one _ _ hl hne)
theorem tau_order_right (j l : PTm n) (hl : Γ ⊢[PRAAx] lt (succ j) l) : Γ ⊢[PRAAx] lt (tau j (succ j)) (tau j l) :=
  lt_congr (tau_right _).eqSymm
    (tau_other _ _ (different_symm (different_of_lt (lt_of_le_of_lt (le_succ_self _) hl))) (different_symm (different_of_lt hl))).eqSymm
    (lt_of_le_of_lt (le_succ_self _) hl)
theorem tau_order_before (j i : PTm n) (hi : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx] lt (tau j i) (tau j j) :=
  lt_congr (tau_before _ _ hi).eqSymm (tau_left _).eqSymm (lt_of_lt_of_le hi (le_succ_self _))
theorem tau_order_before_right (j i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ j))
    (hne : Γ ⊢[PRAAx] neg (i ≐ j)) : Γ ⊢[PRAAx] lt (tau j i) (tau j (succ j)) :=
  lt_congr (tau_other _ _ hne (different_of_lt hi)).eqSymm (tau_right _).eqSymm (before_one _ _ hi hne)

/-- Away from the ordered adjacent pair, an increasing pair stays increasing. -/
theorem tau_order_forward (j i l : PTm n) (hil : Γ ⊢[PRAAx] lt i l)
    (hpair : Γ ⊢[PRAAx] neg (pairT i l ≐ pairT j (succ j))) : Γ ⊢[PRAAx] lt (tau j i) (tau j l) := by
  refine .orE (eq_or_ne i j) ?_ ?_
  · have hlt : (i ≐ j) :: Γ ⊢[PRAAx] lt j l := lt_congr Prf.hyp0 (.eqRefl _) hil.wk
    have no : (i ≐ j) :: Γ ⊢[PRAAx] neg (l ≐ succ j) :=
      .impI (.impE hpair.wk.wk (congrPairT Prf.hyp1 Prf.hyp0))
    exact lt_congr (tau_congr (.eqRefl _) Prf.hyp0).eqSymm (.eqRefl _) (tau_order_left _ _ hlt no)
  · refine .orE (eq_or_ne i (succ j)) ?_ ?_
    · exact lt_congr (tau_congr (.eqRefl _) Prf.hyp0).eqSymm (.eqRefl _)
        (tau_order_right _ _ (lt_congr Prf.hyp0 (.eqRefl _) hil.wk.wk))
    · refine .orE (eq_or_ne l j) ?_ ?_
      · exact lt_congr (.eqRefl _) (tau_congr (.eqRefl _) Prf.hyp0).eqSymm
          (tau_order_before _ _ (lt_congr (.eqRefl _) Prf.hyp0 hil.wk.wk.wk))
      · refine .orE (eq_or_ne l (succ j)) ?_ ?_
        · exact lt_congr (.eqRefl _) (tau_congr (.eqRefl _) Prf.hyp0).eqSymm
            (tau_order_before_right _ _ (lt_congr (.eqRefl _) Prf.hyp0 hil.wk.wk.wk.wk) (.hyp (by simp)))
        · exact lt_congr (tau_other _ _ (.hyp (by simp)) (.hyp (by simp))).eqSymm
            (tau_other _ _ (.hyp (by simp)) (.hyp (by simp))).eqSymm hil.wk.wk.wk.wk

theorem tau_order_iff (j i l : PTm n)
    (hf : Γ ⊢[PRAAx] neg (pairT i l ≐ pairT j (succ j)))
    (hr : Γ ⊢[PRAAx] neg (pairT i l ≐ pairT (succ j) j)) : Γ ⊢[PRAAx]
    Fm.iff (lt i l) (lt (tau j i) (tau j l)) := by
  refine .iffI (.impI (tau_order_forward _ _ _ Prf.hyp0 hf.wk)) (.impI ?_)
  have no : lt (tau j i) (tau j l) :: Γ ⊢[PRAAx]
      neg (pairT (tau j i) (tau j l) ≐ pairT j (succ j)) := by
    refine .impI ?_
    let Δ := (pairT (tau j i) (tau j l) ≐ pairT j (succ j)) :: lt (tau j i) (tau j l) :: Γ
    have ep : Δ ⊢[PRAAx] pairT (tau j i) (tau j l) ≐ pairT j (succ j) := Prf.hyp0
    have ei : Δ ⊢[PRAAx] i ≐ succ j := (tau_involution j i).eqSymm.eqTrans ((tau_congr (.eqRefl _) (pair_first ep)).eqTrans (tau_left _))
    have el : Δ ⊢[PRAAx] l ≐ j := (tau_involution j l).eqSymm.eqTrans ((tau_congr (.eqRefl _) (pair_second ep)).eqTrans (tau_right _))
    exact .impE hr.wk.wk (congrPairT ei el)
  exact lt_congr (tau_involution _ _) (tau_involution _ _) (tau_order_forward _ _ _ Prf.hyp0 no)

/-! The exceptional ordered pairs are handled by actual Boolean/delta
values; every other inversion bit is transported through its reflection. -/
def pairDelta (i l a b : PTm n) : PTm n := eqb i a*eqb l b
ipra_subst pairDelta
theorem delta_one (i l a b : PTm n) (h : Γ ⊢[PRAAx] pairT i l ≐ pairT a b) : Γ ⊢[PRAAx] pairDelta i l a b ≐ one :=
  (congrMul (eqb_of_eq (pair_first h)) (eqb_of_eq (pair_second h))).eqTrans (one_mul _)
theorem delta_zero (i l a b : PTm n) (h : Γ ⊢[PRAAx] neg (pairT i l ≐ pairT a b)) : Γ ⊢[PRAAx] pairDelta i l a b ≐ zero := by
  refine .orE (eq_or_ne i a) ?_ ?_
  · refine .orE (eq_or_ne l b) ?_ ?_
    · exact .botE _ (.impE h.wk.wk (congrPairT Prf.hyp1 Prf.hyp0))
    · exact (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (mul_zero _)
  · exact (congrMul (eqb_of_ne Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _)
theorem inversion_congr {m m' w w' i i' l l' : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ m') (hw : Γ ⊢[PRAAx] w ≐ w')
    (hi : Γ ⊢[PRAAx] i ≐ i') (hl : Γ ⊢[PRAAx] l ≐ l') : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversionBit m w i l ≐ RuntimePermutationWords.inversionBit m' w' i' l' := by
  ipra_congr (RuntimePermutationWords.inversionBit (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hm, hw, hi, hl]
theorem inversion_zero_position (m w i l : PTm n) (h : Γ ⊢[PRAAx] le l i) : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversionBit m w i l ≐ zero :=
  .orE (RuntimePermutationWords.inversion_cases _ _ _ _) Prf.hyp0
    (le_lt_absurd _ h.wk (.andE₁ ((RuntimePermutationWords.inversion_reflection _ _ _ _).iffMp Prf.hyp0)))
theorem bits_equal (a b : PTm n)
    (ha : Γ ⊢[PRAAx] (a ≐ zero) ⋎ (a ≐ one)) (hb : Γ ⊢[PRAAx] (b ≐ zero) ⋎ (b ≐ one))
    (h : Γ ⊢[PRAAx] Fm.iff (a ≐ one) (b ≐ one)) : Γ ⊢[PRAAx] a ≐ b := by
  refine .orE ha ?_ ?_
  · refine .orE hb.wk (Prf.hyp1.eqTrans Prf.hyp0.eqSymm) ?_
    exact .botE _ (BoundedReflection.one_ne_zero _ ((h.wk.wk.iffMpr Prf.hyp0).eqSymm.eqTrans Prf.hyp1))
  · exact Prf.hyp0.eqTrans (h.wk.iffMp Prf.hyp0).eqSymm

theorem inversion_transport (m u v i l k q : PTm n)
    (hpos : Γ ⊢[PRAAx] Fm.iff (lt i l) (lt k q))
    (hi : Γ ⊢[PRAAx] RuntimePermutationWords.digit m u i ≐ RuntimePermutationWords.digit m v k)
    (hl : Γ ⊢[PRAAx] RuntimePermutationWords.digit m u l ≐ RuntimePermutationWords.digit m v q) : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversionBit m u i l ≐ RuntimePermutationWords.inversionBit m v k q := by
  apply bits_equal _ _ (RuntimePermutationWords.inversion_cases _ _ _ _) (RuntimePermutationWords.inversion_cases _ _ _ _)
  refine .iffI (.impI ?_) (.impI ?_)
  · have old : (RuntimePermutationWords.inversionBit m u i l ≐ one) :: Γ ⊢[PRAAx]
        lt i l ⋏ lt (RuntimePermutationWords.digit m u l) (RuntimePermutationWords.digit m u i) :=
      (RuntimePermutationWords.inversion_reflection m u i l).iffMp Prf.hyp0
    exact (RuntimePermutationWords.inversion_reflection m v k q).iffMpr
      (.andI (hpos.wk.iffMp (.andE₁ old)) (lt_congr hl.wk hi.wk (.andE₂ old)))
  · have old : (RuntimePermutationWords.inversionBit m v k q ≐ one) :: Γ ⊢[PRAAx]
        lt k q ⋏ lt (RuntimePermutationWords.digit m v q) (RuntimePermutationWords.digit m v k) :=
      (RuntimePermutationWords.inversion_reflection m v k q).iffMp Prf.hyp0
    exact (RuntimePermutationWords.inversion_reflection m u i l).iffMpr
      (.andI (hpos.wk.iffMpr (.andE₁ old)) (lt_congr hl.wk.eqSymm hi.wk.eqSymm (.andE₂ old)))
theorem inversion_outside (m w j i l : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (hi : Γ ⊢[PRAAx] lt i m) (hl : Γ ⊢[PRAAx] lt l m)
    (hf : Γ ⊢[PRAAx] neg (pairT i l ≐ pairT j (succ j)))
    (hr : Γ ⊢[PRAAx] neg (pairT i l ≐ pairT (succ j) j)) : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversionBit m (swapWord m w j) i l ≐
      RuntimePermutationWords.inversionBit m w (tau j i) (tau j l) :=
  inversion_transport _ _ _ _ _ _ _ (tau_order_iff _ _ _ hf hr) (swapped_digit _ _ _ _ hj hi) (swapped_digit _ _ _ _ hj hl)

theorem inversion_point_balance (m w j i l : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (hi : Γ ⊢[PRAAx] lt i m) (hl : Γ ⊢[PRAAx] lt l m) : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversionBit m (swapWord m w j) i l+
        pairDelta i l (succ j) j*RuntimePermutationWords.inversionBit m w j (succ j) ≐
      RuntimePermutationWords.inversionBit m w (tau j i) (tau j l)+
        pairDelta i l j (succ j)*RuntimePermutationWords.inversionBit m (swapWord m w j) j (succ j) := by
  refine .orE (eq_or_ne (pairT i l) (pairT j (succ j))) ?_ ?_
  · let Δ := (pairT i l ≐ pairT j (succ j)) :: Γ
    have ep : Δ ⊢[PRAAx] pairT i l ≐ pairT j (succ j) := Prf.hyp0
    have ef : Δ ⊢[PRAAx] RuntimePermutationWords.inversionBit m (swapWord m w j) i l ≐
        RuntimePermutationWords.inversionBit m (swapWord m w j) j (succ j) :=
      inversion_congr (.eqRefl _) (.eqRefl _) (pair_first ep) (pair_second ep)
    have er : Δ ⊢[PRAAx] RuntimePermutationWords.inversionBit m w (tau j i) (tau j l) ≐ zero :=
      (inversion_congr (.eqRefl _) (.eqRefl _)
        ((tau_congr (.eqRefl _) (pair_first ep)).eqTrans (tau_left _))
        ((tau_congr (.eqRefl _) (pair_second ep)).eqTrans (tau_right _))).eqTrans
          (inversion_zero_position _ _ _ _ (le_succ_self _))
    have no : Δ ⊢[PRAAx] neg (pairT i l ≐ pairT (succ j) j) := by
      refine .impI ?_
      exact .impE (different_of_lt (le_refl (succ j))).wk (pair_first (ep.wk.eqSymm.eqTrans Prf.hyp0))
    refine withEq ef fun a => withEq er fun b => withEq (delta_one _ _ _ _ ep) fun c =>
      withEq (delta_zero _ _ _ _ no) fun d => ?_
    apply deriveNat
    ipra_simps
    rw [a,b,c,d]
    ring
  · refine .orE (eq_or_ne (pairT i l) (pairT (succ j) j)) ?_ ?_
    · let Δ := (pairT i l ≐ pairT (succ j) j) :: neg (pairT i l ≐ pairT j (succ j)) :: Γ
      have ep : Δ ⊢[PRAAx] pairT i l ≐ pairT (succ j) j := Prf.hyp0
      have ef : Δ ⊢[PRAAx] RuntimePermutationWords.inversionBit m (swapWord m w j) i l ≐ zero :=
        (inversion_congr (.eqRefl _) (.eqRefl _) (pair_first ep) (pair_second ep)).eqTrans
          (inversion_zero_position _ _ _ _ (le_succ_self _))
      have er : Δ ⊢[PRAAx] RuntimePermutationWords.inversionBit m w (tau j i) (tau j l) ≐
          RuntimePermutationWords.inversionBit m w j (succ j) :=
        inversion_congr (.eqRefl _) (.eqRefl _)
          ((tau_congr (.eqRefl _) (pair_first ep)).eqTrans (tau_right _))
          ((tau_congr (.eqRefl _) (pair_second ep)).eqTrans (tau_left _))
      refine withEq ef fun a => withEq er fun b => withEq (delta_one _ _ _ _ ep) fun c =>
        withEq (delta_zero _ _ _ _ (Prf.hyp1 : Δ ⊢[PRAAx] neg (pairT i l ≐ pairT j (succ j)))) fun d => ?_
      apply deriveNat
      ipra_simps
      rw [a,b,c,d]
      ring
    · let Δ := neg (pairT i l ≐ pairT (succ j) j) :: neg (pairT i l ≐ pairT j (succ j)) :: Γ
      have eq : Δ ⊢[PRAAx] RuntimePermutationWords.inversionBit m (swapWord m w j) i l ≐
          RuntimePermutationWords.inversionBit m w (tau j i) (tau j l) :=
        inversion_outside _ _ _ _ _ hj.wk.wk hi.wk.wk hl.wk.wk Prf.hyp1 Prf.hyp0
      refine withEq eq fun a =>
        withEq (delta_zero _ _ _ _ (Prf.hyp1 : Δ ⊢[PRAAx] neg (pairT i l ≐ pairT j (succ j)))) fun b =>
        withEq (delta_zero _ _ _ _ (Prf.hyp0 : Δ ⊢[PRAAx] neg (pairT i l ≐ pairT (succ j) j))) fun c => ?_
      apply deriveNat
      ipra_simps
      rw [a,b,c]
      ring

/-! Genuine double sums. Row agreements and additivity are derived from
the checked finite-sum kernels, with both numerical bounds internal. -/
def doubleSum (g : PTm 3) (m p : PTm n) : PTm n := ap2 (sumF (oB g)) m (pairT m p)
def rowEqual (g h : PTm 3) (m p q i : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ inst3 g (Syn.shift i) (var 0) (Syn.shift p) ≐ inst3 h (Syn.shift i) (var 0) (Syn.shift q))
def tableEqual (g h : PTm 3) (m p q : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ rowEqual g h (Syn.shift m) (Syn.shift p) (Syn.shift q) (var 0))
ipra_subst doubleSum
ipra_subst rowEqual [Syn.subst_shift, Syn.shift_subst]
ipra_subst tableEqual [Syn.subst_shift, Syn.shift_subst]
theorem row_equal_at (g h : PTm 3) (m p q i l : PTm n) (he : Γ ⊢[PRAAx] rowEqual g h m p q i)
    (hl : Γ ⊢[PRAAx] lt l m) : Γ ⊢[PRAAx] inst3 g i l p ≐ inst3 h i l q := by
  have gate : Γ ⊢[PRAAx] lt l m ⟶ inst3 g i l p ≐ inst3 h i l q := by
    simpa only [rowEqual,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_inst3,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using he.allE l
  exact .impE gate hl
theorem table_equal_row (g h : PTm 3) (m p q i : PTm n) (he : Γ ⊢[PRAAx] tableEqual g h m p q)
    (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx] rowEqual g h m p q i := by
  have gate : Γ ⊢[PRAAx] lt i m ⟶ rowEqual g h m p q i := by
    simpa only [tableEqual,Fm.subst_imp,subst_lt,subst_rowEqual,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using he.allE i
  exact .impE gate hi

theorem row_entry_at (g : PTm 3) (i l p : PTm n) : Γ ⊢[PRAAx] inst2 (rowB g) l (pairT i p) ≐ inst3 g i l p := by
  rw [inst2_rowB]
  exact congrInst3 g (fst_pair _ _) (.eqRefl _) (snd_pair _ _)
theorem row_sum_congr (g h : PTm 3) (m p q i : PTm n) (he : Γ ⊢[PRAAx] rowEqual g h m p q i) : Γ ⊢[PRAAx]
    ap2 (sumF (rowB g)) m (pairT i p) ≐ ap2 (sumF (rowB h)) m (pairT i q) := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowEqual g h (Syn.shift m) (Syn.shift p) (Syn.shift q) (Syn.shift i) := by
    simpa only [Fm.shift,subst_rowEqual,Syn.shift] using he.shift
  simpa only [Syn.shift,subst_pairT] using (row_entry_at g (Syn.shift i) (var 0) (Syn.shift p)).eqTrans
    ((row_equal_at g h _ _ _ _ _ hs.wk Prf.hyp0).eqTrans (row_entry_at h (Syn.shift i) (var 0) (Syn.shift q)).eqSymm)
theorem double_congr (g h : PTm 3) (m p q : PTm n) (he : Γ ⊢[PRAAx] tableEqual g h m p q) : Γ ⊢[PRAAx]
    doubleSum g m p ≐ doubleSum h m q := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] tableEqual g h (Syn.shift m) (Syn.shift p) (Syn.shift q) := by
    simpa only [Fm.shift,subst_tableEqual,Syn.shift] using he.shift
  simpa only [Syn.shift,subst_pairT] using (oB_at g (var 0) (Syn.shift m) (Syn.shift p)).eqTrans
    ((row_sum_congr _ _ _ _ _ _ (table_equal_row _ _ _ _ _ _ hs.wk Prf.hyp0)).eqTrans
      (oB_at h (var 0) (Syn.shift m) (Syn.shift q)).eqSymm)

theorem double_add (g h : PTm 3) (m p : PTm n) : Γ ⊢[PRAAx]
    doubleSum (g+h) m p ≐ doubleSum g m p+doubleSum h m p := by
  have rowSyntax : rowB (g+h) = addBody (rowB g) (rowB h) := by simp [rowB,addBody]
  have rows : Γ ⊢[PRAAx] doubleSum (g+h) m p ≐ ap2 (sumF (addBody (oB g) (oB h))) m (pairT m p) := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    rw [inst2_addBody]
    have e := (oB_at (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) (g+h) (var 0) (Syn.shift m) (Syn.shift p))
    rw [rowSyntax] at e
    simpa only [Syn.shift,subst_pairT] using e.eqTrans
      ((sum_add (rowB g) (rowB h) (Syn.shift m) (pairT (var 0) (Syn.shift p))).eqTrans
        (congrAdd (oB_at g (var 0) (Syn.shift m) (Syn.shift p)).eqSymm (oB_at h (var 0) (Syn.shift m) (Syn.shift p)).eqSymm))
  exact rows.eqTrans (sum_add _ _ _ _)

def swapTable (g : PTm 3) : PTm 3 := inst3 g (tau (fstT (var 2)) (var 0))
  (tau (fstT (var 2)) (var 1)) (sndT (var 2))
theorem swap_table_at (g : PTm 3) (j i l p : PTm n) : Γ ⊢[PRAAx]
    inst3 (swapTable g) i l (pairT j p) ≐ inst3 g (tau j i) (tau j l) p := by
  have vector : (fun k => Syn.subst ![i,l,pairT j p]
      ((![tau (fstT (var 2)) (var 0),tau (fstT (var 2)) (var 1),sndT (var 2)] : Fin 3 → PTm 3) k)) =
      ![tau (fstT (pairT j p)) i,tau (fstT (pairT j p)) l,sndT (pairT j p)] := by
    funext k
    fin_cases k <;> simp
  simp only [swapTable,inst3,Syn.subst_subst]
  rw [vector]
  exact congrInst3 g (tau_congr (fst_pair _ _) (.eqRefl _)) (tau_congr (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)
theorem row_swap_sum (g : PTm 3) (m j i p : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    ap2 (sumF (rowB (swapTable g))) m (pairT i (pairT j p)) ≐ ap2 (sumF (rowB g)) m (pairT (tau j i) p) := by
  have bridge : Γ ⊢[PRAAx] ap2 (sumF (rowB (swapTable g))) m (pairT i (pairT j p)) ≐
      ap2 (sumF (sumSwapBody (rowB g))) m (pairT j (pairT (tau j i) p)) := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (rowB (swapTable g)) (var 0) (pairT (Syn.shift i) (pairT (Syn.shift j) (Syn.shift p))) ≐
        inst2 (sumSwapBody (rowB g)) (var 0) (pairT (Syn.shift j) (pairT (tau (Syn.shift j) (Syn.shift i)) (Syn.shift p))) :=
      (row_entry_at (swapTable g) _ _ _).eqTrans ((swap_table_at g _ _ _ _).eqTrans
        ((row_entry_at g _ _ _).eqSymm.eqTrans (sum_swap_body_at (rowB g) _ _ _).eqSymm))
    simpa only [Δ,Syn.shift,subst_pairT,subst_tau] using e
  exact bridge.eqTrans (adjacent_sum (rowB g) _ _ _ hj)
theorem double_swap (g : PTm 3) (m j p : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    doubleSum (swapTable g) m (pairT j p) ≐ doubleSum g m p := by
  have bridge : Γ ⊢[PRAAx] doubleSum (swapTable g) m (pairT j p) ≐
      ap2 (sumF (sumSwapBody (oB g))) m (pairT j (pairT m p)) := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    have js : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
      simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (oB (swapTable g)) (var 0) (pairT (Syn.shift m) (pairT (Syn.shift j) (Syn.shift p))) ≐
        inst2 (sumSwapBody (oB g)) (var 0) (pairT (Syn.shift j) (pairT (Syn.shift m) (Syn.shift p))) :=
      (oB_at (swapTable g) _ _ _).eqTrans ((row_swap_sum g _ _ _ _ js.wk).eqTrans
        ((oB_at g _ _ _).eqSymm.eqTrans (sum_swap_body_at (oB g) _ _ _).eqSymm))
    simpa only [Δ,Syn.shift,subst_pairT] using e
  exact bridge.eqTrans (adjacent_sum (oB g) _ _ _ hj)

def deltaData (a b v : PTm n) : PTm n := pairT a (pairT b v)
def deltaTable : PTm 3 := pairDelta (var 0) (var 1) (fstT (var 2)) (fstT (sndT (var 2)))*sndT (sndT (var 2))
ipra_subst deltaData
alias eqb_congr := Common.congrEqb
theorem eqb_symmetric (a b : PTm n) : Γ ⊢[PRAAx] eqb a b ≐ eqb b a := congrMonus (.eqRefl _) (add_comm _ _)
theorem delta_table_at (a b v i l : PTm n) : Γ ⊢[PRAAx]
    inst3 deltaTable i l (deltaData a b v) ≐ pairDelta i l a b*v := by
  simp only [deltaTable,inst3,PTm.subst_mul,subst_pairDelta,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  have tail := snd_pair (Γ := Γ) a (pairT b v)
  exact congrMul (congrMul (eqb_congr (.eqRefl _) (fst_pair _ _))
    (eqb_congr (.eqRefl _) ((congrFst tail).eqTrans (fst_pair _ _))))
      ((congrSnd tail).eqTrans (snd_pair _ _))

theorem delta_body_at (b v l : PTm n) : Γ ⊢[PRAAx] inst2 (dB (var 1 : PTm 2)) l (pairT b v) ≐ eqb b l*v := by
  rw [inst2_dB]
  exact congrMul (eqb_congr (fst_pair _ _) (.eqRefl _)) (by simpa only [inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using snd_pair b v)
theorem delta_pair_reorder (i l a b v : PTm n) : Γ ⊢[PRAAx]
    pairDelta i l a b*v ≐ eqb b l*(eqb i a*v) := by
  refine withEq (eqb_symmetric (Γ := Γ) l b) fun e => ?_
  apply deriveNat
  simp only [pairDelta]
  ipra_simps
  rw [e]
  ring

theorem row_delta (m a b v i : PTm n) (hb : Γ ⊢[PRAAx] lt b m) : Γ ⊢[PRAAx]
    ap2 (sumF (rowB deltaTable)) m (pairT i (deltaData a b v)) ≐ eqb i a*v := by
  have bridge : Γ ⊢[PRAAx] ap2 (sumF (rowB deltaTable)) m (pairT i (deltaData a b v)) ≐
      ap2 (sumF (dB (var 1 : PTm 2))) m (pairT b (eqb i a*v)) := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (rowB deltaTable) (var 0) (pairT (Syn.shift i) (deltaData (Syn.shift a) (Syn.shift b) (Syn.shift v))) ≐
        inst2 (dB (var 1 : PTm 2)) (var 0) (pairT (Syn.shift b) (eqb (Syn.shift i) (Syn.shift a)*Syn.shift v)) :=
      (row_entry_at deltaTable _ _ _).eqTrans ((delta_table_at _ _ _ _ _).eqTrans
        ((delta_pair_reorder _ _ _ _ _).eqTrans (delta_body_at _ _ _).eqSymm))
    simpa only [Δ,Syn.shift,subst_pairT,subst_deltaData,PTm.subst_mul,subst_eqb] using e
  exact bridge.eqTrans (by simpa only [inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using sum_delta (var 1 : PTm 2) (x := eqb i a*v) hb)
theorem double_delta (m a b v : PTm n) (ha : Γ ⊢[PRAAx] lt a m) (hb : Γ ⊢[PRAAx] lt b m) : Γ ⊢[PRAAx]
    doubleSum deltaTable m (deltaData a b v) ≐ v := by
  have bridge : Γ ⊢[PRAAx] doubleSum deltaTable m (deltaData a b v) ≐ ap2 (sumF (dB (var 1 : PTm 2))) m (pairT a v) := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    have bs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift b) (Syn.shift m) := by
      simpa only [Fm.shift,subst_lt,Syn.shift] using hb.shift
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (oB deltaTable) (var 0) (pairT (Syn.shift m) (deltaData (Syn.shift a) (Syn.shift b) (Syn.shift v))) ≐
        inst2 (dB (var 1 : PTm 2)) (var 0) (pairT (Syn.shift a) (Syn.shift v)) :=
      (oB_at deltaTable _ _ _).eqTrans ((row_delta _ _ _ _ _ bs.wk).eqTrans
        ((congrMul (eqb_symmetric _ _) (.eqRefl _)).eqTrans (delta_body_at _ _ _).eqSymm))
    simpa only [Δ,Syn.shift,subst_pairT,subst_deltaData] using e
  exact bridge.eqTrans (by simpa only [inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using sum_delta (var 1 : PTm 2) (x := v) ha)

def inversionTable : PTm 3 := RuntimePermutationWords.inversionBit (sndT (var 2)) (fstT (var 2)) (var 0) (var 1)
theorem inversion_table_at (m w i l : PTm n) : Γ ⊢[PRAAx]
    inst3 inversionTable i l (RuntimePermutationWords.data m w) ≐ RuntimePermutationWords.inversionBit m w i l := by
  simp only [inversionTable,inst3,RuntimePermutationWords.subst_inversionBit,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,RuntimePermutationWords.data]
  exact inversion_congr (snd_pair _ _) (fst_pair _ _) (.eqRefl _) (.eqRefl _)
theorem inversion_row_bridge (m w i : PTm n) : Γ ⊢[PRAAx]
    ap2 (sumF (rowB inversionTable)) m (pairT i (RuntimePermutationWords.data m w)) ≐ RuntimePermutationWords.rowPrefix m w i m := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have e : Δ ⊢[PRAAx] inst2 (rowB inversionTable) (var 0) (pairT (Syn.shift i) (RuntimePermutationWords.data (Syn.shift m) (Syn.shift w))) ≐
      inst2 RuntimePermutationWords.inversionColumn (var 0) (pairT (Syn.shift i) (RuntimePermutationWords.data (Syn.shift m) (Syn.shift w))) :=
    (row_entry_at inversionTable _ _ _).eqTrans ((inversion_table_at _ _ _ _).eqTrans (RuntimePermutationWords.inversion_column_at _ _ _ _).eqSymm)
  simpa only [Δ,Syn.shift,subst_pairT,RuntimePermutationWords.subst_data] using e
theorem inversion_double_bridge (m w : PTm n) : Γ ⊢[PRAAx]
    doubleSum inversionTable m (RuntimePermutationWords.data m w) ≐ RuntimePermutationWords.inversions m w := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have e : Δ ⊢[PRAAx] inst2 (oB inversionTable) (var 0) (pairT (Syn.shift m) (RuntimePermutationWords.data (Syn.shift m) (Syn.shift w))) ≐
      inst2 RuntimePermutationWords.inversionRow (var 0) (RuntimePermutationWords.data (Syn.shift m) (Syn.shift w)) :=
    (oB_at inversionTable _ _ _).eqTrans ((inversion_row_bridge _ _ _).eqTrans (RuntimePermutationWords.inversion_row_at _ _ _).eqSymm)
  simpa only [Δ,Syn.shift,subst_pairT,RuntimePermutationWords.subst_data] using e

/-! Fixed-syntax reparameterization keeps all numerical data inside actual
unary bodies. It introduces no evaluator or semantic composition premise. -/
def at1 (f : PTm 1) (p : PTm n) : PTm n := Syn.subst ![p] f
def mapTable (g : PTm 3) (f : PTm 1) : PTm 3 := inst3 g (var 0) (var 1) (at1 f (var 2))
@[simp] theorem subst_at1 {k : ℕ} (σ : Fin n → PTm k) (f : PTm 1) (p : PTm n) :
    Syn.subst σ (at1 f p) = at1 f (Syn.subst σ p) := by
  simp only [at1,Syn.subst_subst]
  congr 1
  funext i
  fin_cases i
  rfl
theorem map_table_at (g : PTm 3) (f : PTm 1) (i l p : PTm n) :
    inst3 (mapTable g f) i l p = inst3 g i l (at1 f p) := by
  have vector : (fun k => Syn.subst ![i,l,p]
      ((![var 0,var 1,at1 f (var 2)] : Fin 3 → PTm 3) k)) = ![i,l,at1 f p] := by
    funext k
    fin_cases k
    · rfl
    · rfl
    · exact subst_at1 ![i,l,p] f (var 2)
  simp only [mapTable,inst3,Syn.subst_subst]
  rw [vector]

theorem double_map (g : PTm 3) (f : PTm 1) (m p : PTm n) : Γ ⊢[PRAAx]
    doubleSum (mapTable g f) m p ≐ doubleSum g m (at1 f p) := by
  apply double_congr
  refine .allI (.impI (.allI (.impI ?_)))
  simp only [Syn.shift,subst_at1,map_table_at]
  exact .eqRefl _
theorem double_data_congr (g : PTm 3) (m : PTm n) {p q : PTm n} (h : Γ ⊢[PRAAx] p ≐ q) : Γ ⊢[PRAAx]
    doubleSum g m p ≐ doubleSum g m q := congrAp2 (sumF (oB g)) (.eqRefl _) (congrPairT (.eqRefl _) h)

def baseData (m w j : PTm n) : PTm n := pairT m (pairT w j)
def packedBody (t : PTm 3) : PTm 1 := Syn.subst ![fstT (var 0),fstT (sndT (var 0)),sndT (sndT (var 0))] t
@[simp] theorem subst_baseData {k : ℕ} (σ : Fin n → PTm k) (m w j : PTm n) :
    Syn.subst σ (baseData m w j) = baseData (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ j) := by simp [baseData]
theorem packed_at (t : PTm 3) (m w j : PTm n) : Γ ⊢[PRAAx]
    at1 (packedBody t) (baseData m w j) ≐ Syn.subst ![m,w,j] t := by
  have vector : (fun k => Syn.subst ![baseData m w j]
      ((![fstT (var 0),fstT (sndT (var 0)),sndT (sndT (var 0))] : Fin 3 → PTm 1) k)) =
      ![fstT (baseData m w j),fstT (sndT (baseData m w j)),sndT (sndT (baseData m w j))] := by
    funext k
    fin_cases k <;> simp
  simp only [at1,packedBody,Syn.subst_subst]
  rw [vector]
  have tail := snd_pair (Γ := Γ) m (pairT w j)
  exact Prf.eqCongr (Ax := PRAAx) (Γ := Γ) t
    (σ := ![fstT (baseData m w j),fstT (sndT (baseData m w j)),sndT (sndT (baseData m w j))])
    (σ' := ![m,w,j]) (fun k => by
      fin_cases k
      · exact fst_pair _ _
      · exact (congrFst tail).eqTrans (fst_pair _ _)
      · exact (congrSnd tail).eqTrans (snd_pair _ _))

def newDataBody : PTm 1 := packedBody (RuntimePermutationWords.data (var 0) (swapWord (var 0) (var 1) (var 2)))
def reorderedDataBody : PTm 1 := packedBody (pairT (var 2) (RuntimePermutationWords.data (var 0) (var 1)))
def oldDeltaDataBody : PTm 1 := packedBody (deltaData (succ (var 2)) (var 2)
  (RuntimePermutationWords.inversionBit (var 0) (var 1) (var 2) (succ (var 2))))
def newDeltaDataBody : PTm 1 := packedBody (deltaData (var 2) (succ (var 2))
  (RuntimePermutationWords.inversionBit (var 0) (swapWord (var 0) (var 1) (var 2)) (var 2) (succ (var 2))))
def newInversionTable : PTm 3 := mapTable inversionTable newDataBody
def reorderedInversionTable : PTm 3 := mapTable (swapTable inversionTable) reorderedDataBody
def oldDeltaTable : PTm 3 := mapTable deltaTable oldDeltaDataBody
def newDeltaTable : PTm 3 := mapTable deltaTable newDeltaDataBody

theorem new_data_at (m w j : PTm n) : Γ ⊢[PRAAx]
    at1 newDataBody (baseData m w j) ≐ RuntimePermutationWords.data m (swapWord m w j) := by
  simpa [newDataBody] using packed_at (Γ := Γ)
    (RuntimePermutationWords.data (var 0) (swapWord (var 0) (var 1) (var 2)) : PTm 3) m w j
theorem reordered_data_at (m w j : PTm n) : Γ ⊢[PRAAx]
    at1 reorderedDataBody (baseData m w j) ≐ pairT j (RuntimePermutationWords.data m w) := by
  simpa [reorderedDataBody] using packed_at (Γ := Γ) (pairT (var 2) (RuntimePermutationWords.data (var 0) (var 1)) : PTm 3) m w j
theorem old_delta_data_at (m w j : PTm n) : Γ ⊢[PRAAx] at1 oldDeltaDataBody (baseData m w j) ≐
    deltaData (succ j) j (RuntimePermutationWords.inversionBit m w j (succ j)) := by
  simpa [oldDeltaDataBody] using packed_at (Γ := Γ) (deltaData (succ (var 2)) (var 2)
    (RuntimePermutationWords.inversionBit (var 0) (var 1) (var 2) (succ (var 2))) : PTm 3) m w j
theorem new_delta_data_at (m w j : PTm n) : Γ ⊢[PRAAx] at1 newDeltaDataBody (baseData m w j) ≐
    deltaData j (succ j) (RuntimePermutationWords.inversionBit m (swapWord m w j) j (succ j)) := by
  simpa [newDeltaDataBody] using packed_at (Γ := Γ) (deltaData (var 2) (succ (var 2))
    (RuntimePermutationWords.inversionBit (var 0) (swapWord (var 0) (var 1) (var 2)) (var 2) (succ (var 2))) : PTm 3) m w j

theorem new_point_at (m w j i l : PTm n) : Γ ⊢[PRAAx] inst3 newInversionTable i l (baseData m w j) ≐
    RuntimePermutationWords.inversionBit m (swapWord m w j) i l := by
  rw [newInversionTable,map_table_at]
  exact (congrInst3 inversionTable (.eqRefl _) (.eqRefl _) (new_data_at _ _ _)).eqTrans (inversion_table_at _ _ _ _)
theorem reordered_point_at (m w j i l : PTm n) : Γ ⊢[PRAAx] inst3 reorderedInversionTable i l (baseData m w j) ≐
    RuntimePermutationWords.inversionBit m w (tau j i) (tau j l) := by
  rw [reorderedInversionTable,map_table_at]
  exact (congrInst3 (swapTable inversionTable) (.eqRefl _) (.eqRefl _) (reordered_data_at _ _ _)).eqTrans
    ((swap_table_at _ _ _ _ _).eqTrans (inversion_table_at _ _ _ _))
theorem old_delta_point_at (m w j i l : PTm n) : Γ ⊢[PRAAx] inst3 oldDeltaTable i l (baseData m w j) ≐
    pairDelta i l (succ j) j*RuntimePermutationWords.inversionBit m w j (succ j) := by
  rw [oldDeltaTable,map_table_at]
  exact (congrInst3 deltaTable (.eqRefl _) (.eqRefl _) (old_delta_data_at _ _ _)).eqTrans (delta_table_at _ _ _ _ _)
theorem new_delta_point_at (m w j i l : PTm n) : Γ ⊢[PRAAx] inst3 newDeltaTable i l (baseData m w j) ≐
    pairDelta i l j (succ j)*RuntimePermutationWords.inversionBit m (swapWord m w j) j (succ j) := by
  rw [newDeltaTable,map_table_at]
  exact (congrInst3 deltaTable (.eqRefl _) (.eqRefl _) (new_delta_data_at _ _ _)).eqTrans (delta_table_at _ _ _ _ _)
theorem balance_point_at (m w j i l : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (hi : Γ ⊢[PRAAx] lt i m) (hl : Γ ⊢[PRAAx] lt l m) : Γ ⊢[PRAAx]
    inst3 (newInversionTable+oldDeltaTable) i l (baseData m w j) ≐
      inst3 (reorderedInversionTable+newDeltaTable) i l (baseData m w j) := by
  simpa only [inst3,PTm.subst_add] using
    (congrAdd (new_point_at (Γ := Γ) m w j i l) (old_delta_point_at m w j i l)).eqTrans
      ((inversion_point_balance _ _ _ _ _ hj hi hl).eqTrans
        (congrAdd (reordered_point_at _ _ _ _ _) (new_delta_point_at _ _ _ _ _)).eqSymm)

theorem balance_tables (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    tableEqual (newInversionTable+oldDeltaTable) (reorderedInversionTable+newDeltaTable) m (baseData m w j) (baseData m w j) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Γ1 := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: Γ1.map Fm.shift
  have js0 : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  have js1 : Γ1 ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := js0.wk
  have js : Δ ⊢[PRAAx] lt (succ (Syn.shift (Syn.shift j))) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,Γ1,List.map_cons,Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using js1.shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,Γ1,List.map_cons,Fm.shift,subst_lt,Syn.subst_var,Syn.shift,Fin.succ_zero_eq_one] using
      (Prf.hyp1 : Δ ⊢[PRAAx] Fm.shift (lt (var 0) (Syn.shift m)))
  have hl : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift m)) := Prf.hyp0
  simpa only [Δ,Γ1,Syn.shift,subst_baseData,Syn.subst_var,Fin.succ_zero_eq_one] using
    balance_point_at (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift j)) (var 1) (var 0) js hi hl

theorem new_double (m w j : PTm n) : Γ ⊢[PRAAx] doubleSum newInversionTable m (baseData m w j) ≐
    RuntimePermutationWords.inversions m (swapWord m w j) :=
  (double_map _ _ _ _).eqTrans ((double_data_congr _ _ (new_data_at _ _ _)).eqTrans (inversion_double_bridge _ _))
theorem reordered_double (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    doubleSum reorderedInversionTable m (baseData m w j) ≐ RuntimePermutationWords.inversions m w :=
  (double_map _ _ _ _).eqTrans ((double_data_congr _ _ (reordered_data_at _ _ _)).eqTrans
    ((double_swap _ _ _ _ hj).eqTrans (inversion_double_bridge _ _)))
theorem old_delta_double (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    doubleSum oldDeltaTable m (baseData m w j) ≐ RuntimePermutationWords.inversionBit m w j (succ j) :=
  (double_map _ _ _ _).eqTrans ((double_data_congr _ _ (old_delta_data_at _ _ _)).eqTrans
    (double_delta _ _ _ _ hj (lt_of_le_of_lt (le_succ_self _) hj)))
theorem new_delta_double (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    doubleSum newDeltaTable m (baseData m w j) ≐ RuntimePermutationWords.inversionBit m (swapWord m w j) j (succ j) :=
  (double_map _ _ _ _).eqTrans ((double_data_congr _ _ (new_delta_data_at _ _ _)).eqTrans
    (double_delta _ _ _ _ (lt_of_le_of_lt (le_succ_self _) hj) hj))

/-- Exact unsigned conservation for every original word, with no assumption
that its digits are distinct and no horizon restriction. -/
theorem inversion_balance (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversions m (swapWord m w j)+RuntimePermutationWords.inversionBit m w j (succ j) ≐
      RuntimePermutationWords.inversions m w+RuntimePermutationWords.inversionBit m (swapWord m w j) j (succ j) := by
  have sums : Γ ⊢[PRAAx] doubleSum newInversionTable m (baseData m w j)+doubleSum oldDeltaTable m (baseData m w j) ≐
      doubleSum reorderedInversionTable m (baseData m w j)+doubleSum newDeltaTable m (baseData m w j) :=
    (double_add _ _ _ _).eqSymm.eqTrans ((double_congr _ _ _ _ _ (balance_tables _ _ _ hj)).eqTrans (double_add _ _ _ _))
  exact (congrAdd (new_double _ _ _) (old_delta_double _ _ _ hj)).eqSymm.eqTrans
    (sums.eqTrans (congrAdd (reordered_double _ _ _ hj) (new_delta_double _ _ _ hj)))

/-! Complementarity uses only the actual adjacent digit inequality.
The global permutation domain derives that inequality below. -/
theorem old_pair_one (m w j : PTm n)
    (hv : Γ ⊢[PRAAx] lt (RuntimePermutationWords.digit m w (succ j)) (RuntimePermutationWords.digit m w j)) : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversionBit m w j (succ j) ≐ one :=
  (RuntimePermutationWords.inversion_reflection _ _ _ _).iffMpr (.andI (le_refl _) hv)
theorem new_pair_values (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    (RuntimePermutationWords.digit m (swapWord m w j) j ≐ RuntimePermutationWords.digit m w (succ j)) ⋏
      (RuntimePermutationWords.digit m (swapWord m w j) (succ j) ≐ RuntimePermutationWords.digit m w j) :=
  .andI ((swapped_digit _ _ _ _ hj (lt_of_le_of_lt (le_succ_self _) hj)).eqTrans
      (digit_congr (.eqRefl _) (.eqRefl _) (tau_left _)))
    ((swapped_digit _ _ _ _ hj hj).eqTrans (digit_congr (.eqRefl _) (.eqRefl _) (tau_right _)))
theorem new_pair_one (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (hv : Γ ⊢[PRAAx] lt (RuntimePermutationWords.digit m w j) (RuntimePermutationWords.digit m w (succ j))) : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversionBit m (swapWord m w j) j (succ j) ≐ one := by
  have vals := new_pair_values m w j hj
  exact (RuntimePermutationWords.inversion_reflection _ _ _ _).iffMpr
    (.andI (le_refl _) (lt_congr (Prf.andE₂ vals).eqSymm (Prf.andE₁ vals).eqSymm hv))
theorem new_pair_lt (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (h : Γ ⊢[PRAAx] RuntimePermutationWords.inversionBit m (swapWord m w j) j (succ j) ≐ one) : Γ ⊢[PRAAx]
    lt (RuntimePermutationWords.digit m w j) (RuntimePermutationWords.digit m w (succ j)) :=
  lt_congr (.andE₂ (new_pair_values _ _ _ hj)) (.andE₁ (new_pair_values _ _ _ hj))
    (.andE₂ ((RuntimePermutationWords.inversion_reflection _ _ _ _).iffMp h))

theorem pair_bits_sum (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (hne : Γ ⊢[PRAAx] neg (RuntimePermutationWords.digit m w j ≐ RuntimePermutationWords.digit m w (succ j))) : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversionBit m w j (succ j)+RuntimePermutationWords.inversionBit m (swapWord m w j) j (succ j) ≐ one := by
  refine .orE (lt_or_le (RuntimePermutationWords.digit m w j) (RuntimePermutationWords.digit m w (succ j))) ?_ ?_
  · have hn : lt (RuntimePermutationWords.digit m w j) (RuntimePermutationWords.digit m w (succ j)) :: Γ ⊢[PRAAx]
        RuntimePermutationWords.inversionBit m w j (succ j) ≐ zero := by
      refine .orE (RuntimePermutationWords.inversion_cases _ _ _ _) Prf.hyp0 ?_
      exact le_lt_absurd _ (le_of_lt (Prf.hyp1))
        (.andE₂ ((RuntimePermutationWords.inversion_reflection _ _ _ _).iffMp Prf.hyp0))
    exact (congrAdd hn (new_pair_one _ _ _ hj.wk Prf.hyp0)).eqTrans (zero_add _)
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · have hn : lt (RuntimePermutationWords.digit m w (succ j)) (RuntimePermutationWords.digit m w j) ::
          le (RuntimePermutationWords.digit m w (succ j)) (RuntimePermutationWords.digit m w j) :: Γ ⊢[PRAAx]
          RuntimePermutationWords.inversionBit m (swapWord m w j) j (succ j) ≐ zero := by
        refine .orE (RuntimePermutationWords.inversion_cases _ _ _ _) Prf.hyp0 ?_
        exact le_lt_absurd _ (le_of_lt (Prf.hyp1)) (new_pair_lt _ _ _ hj.wk.wk.wk Prf.hyp0)
      exact (congrAdd (old_pair_one _ _ _ Prf.hyp0) hn).eqTrans (add_zero _)
    · exact .botE _ (.impE hne.wk.wk Prf.hyp0.eqSymm)

/-- The count change is expressed without subtraction or cancellation of
possibly zero counts: I(swapped)+2*b_old=I(original)+1. -/
theorem inversion_odd_balance (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (hne : Γ ⊢[PRAAx] neg (RuntimePermutationWords.digit m w j ≐ RuntimePermutationWords.digit m w (succ j))) : Γ ⊢[PRAAx]
    RuntimePermutationWords.inversions m (swapWord m w j)+two*RuntimePermutationWords.inversionBit m w j (succ j) ≐
      RuntimePermutationWords.inversions m w+one := by
  ipra_lc natEq (inversion_balance m w j hj)+natEq (pair_bits_sum m w j hj hne)
theorem parity_flip (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (hne : Γ ⊢[PRAAx] neg (RuntimePermutationWords.digit m w j ≐ RuntimePermutationWords.digit m w (succ j))) : Γ ⊢[PRAAx]
    RuntimePermutationWords.parity m (swapWord m w j) ≐ monus one (RuntimePermutationWords.parity m w) :=
  (par_add_two _ _).eqSymm.eqTrans ((congrAp1 parF (inversion_odd_balance _ _ _ hj hne)).eqTrans
    ((congrAp1 parF (succ_eq_add_one _).eqSymm).eqTrans (par_succ _)))

theorem adjacent_digits_different (m w j : PTm n) (h : Γ ⊢[PRAAx] RuntimePermutationWords.permutation m w)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    neg (RuntimePermutationWords.digit m w j ≐ RuntimePermutationWords.digit m w (succ j)) := by
  have no := different_symm (RuntimePermutationWords.distinct_at _ _ _ _ (.andE₂ (.andE₂ h)) hj (le_refl (succ j)))
  refine .impI (.impE no.wk ?_)
  exact (RuntimePermutationWords.word_lookup _ _ _ (lt_of_le_of_lt (le_succ_self _) hj)).wk.eqTrans
    (Prf.hyp0.eqTrans (RuntimePermutationWords.word_lookup _ _ _ hj).wk.eqSymm)
theorem retained_parity_flip (m j t : PTm n) (ht : Γ ⊢[PRAAx] lt t (RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    RuntimePermutationWords.parity m (entry (RuntimePermutationWords.words m) (rankSwap m j t)) ≐
      monus one (RuntimePermutationWords.parity m (entry (RuntimePermutationWords.words m) t)) := by
  have e : Γ ⊢[PRAAx] RuntimePermutationWords.parity m (entry (RuntimePermutationWords.words m) (rankSwap m j t)) ≐
      RuntimePermutationWords.parity m (swapWord m (entry (RuntimePermutationWords.words m) t) j) := by
    ipra_congr (RuntimePermutationWords.parity (var 0) (var 1) : PTm 2) with
      [.eqRefl m, .andE₂ (retained_transport _ _ _ ht hj)]
  exact e.eqTrans (parity_flip _ _ _ hj (adjacent_digits_different _ _ _ (RuntimePermutationWords.retained_valid _ _ ht) hj))

theorem word_no_fixed (m w j : PTm n) (h : Γ ⊢[PRAAx] RuntimePermutationWords.permutation m w)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx] neg (swapWord m w j ≐ w) := by
  refine .impI (.impE (adjacent_digits_different _ _ _ h hj).wk ?_)
  exact (digit_congr (.eqRefl _) Prf.hyp0 (.eqRefl j)).eqSymm.eqTrans
    (Prf.andE₁ (new_pair_values _ _ _ hj.wk))
theorem rank_no_fixed (m j t : PTm n) (ht : Γ ⊢[PRAAx] lt t (RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx] neg (rankSwap m j t ≐ t) := by
  refine .impI (.impE (word_no_fixed _ _ _ (RuntimePermutationWords.retained_valid _ _ ht) hj).wk ?_)
  exact (Prf.andE₂ (retained_transport _ _ _ ht hj)).wk.eqSymm.eqTrans
    (entry_congr (.eqRefl _) Prf.hyp0)

/-! The word and retained-rank programs expose their actual numerical
outputs. Their parity fields are unsigned bits; even/odd Gaussian signs
are a separate consumer of this finite arithmetic certificate. -/
def wordOutput (m w j : PTm n) : PTm n := pairT (swapWord m w j)
  (pairT (swapTuple (RuntimePermutationWords.word m w) m j)
    (pairT (RuntimePermutationWords.parity m (swapWord m w j))
      (RuntimePermutationWords.inversions m (swapWord m w j))))
def wordOutputF : PR 3 := PTm.toPR (wordOutput (var 0) (var 1) (var 2))
def wordRun (m w j : PTm n) : PTm n := ap3 wordOutputF m w j
def rankOutput (m j t : PTm n) : PTm n := pairT (rankSwap m j t)
  (pairT (entry (RuntimePermutationWords.words m) (rankSwap m j t))
    (RuntimePermutationWords.parity m (entry (RuntimePermutationWords.words m) (rankSwap m j t))))
def rankOutputF : PR 3 := PTm.toPR (rankOutput (var 0) (var 1) (var 2))
def rankRun (m j t : PTm n) : PTm n := ap3 rankOutputF m j t
ipra_subst wordOutput
ipra_subst wordRun
ipra_subst rankOutput
ipra_subst rankRun
theorem word_program_at (m w j : PTm n) : Γ ⊢[PRAAx] wordRun m w j ≐ wordOutput m w j := by
  simpa [wordRun,wordOutputF,ap3] using toPR_eq (Γ := Γ) (wordOutput (var 0) (var 1) (var 2)) ![m,w,j]
theorem rank_program_at (m j t : PTm n) : Γ ⊢[PRAAx] rankRun m j t ≐ rankOutput m j t := by
  simpa [rankRun,rankOutputF,ap3] using toPR_eq (Γ := Γ) (rankOutput (var 0) (var 1) (var 2)) ![m,j,t]
theorem returned_word (m w j : PTm n) : Γ ⊢[PRAAx] fstT (wordRun m w j) ≐ swapWord m w j :=
  (congrFst (word_program_at _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tuple (m w j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (wordRun m w j)) ≐ swapTuple (RuntimePermutationWords.word m w) m j :=
  (congrFst ((congrSnd (word_program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_parity (m w j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (wordRun m w j))) ≐ RuntimePermutationWords.parity m (swapWord m w j) :=
  (congrFst ((congrSnd ((congrSnd (word_program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_inversions (m w j : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (wordRun m w j))) ≐ RuntimePermutationWords.inversions m (swapWord m w j) :=
  (congrSnd ((congrSnd ((congrSnd (word_program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_rank (m j t : PTm n) : Γ ⊢[PRAAx] fstT (rankRun m j t) ≐ rankSwap m j t :=
  (congrFst (rank_program_at _ _ _)).eqTrans (fst_pair _ _)
theorem returned_rank_word (m j t : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (rankRun m j t)) ≐ entry (RuntimePermutationWords.words m) (rankSwap m j t) :=
  (congrFst ((congrSnd (rank_program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_rank_parity (m j t : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (rankRun m j t)) ≐ RuntimePermutationWords.parity m (entry (RuntimePermutationWords.words m) (rankSwap m j t)) :=
  (congrSnd ((congrSnd (rank_program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_word_bound (m w j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    lt (fstT (wordRun m w j)) (RuntimePermutationWords.horizon m) :=
  lt_congr (returned_word _ _ _).eqSymm (.eqRefl _) (swapped_bound _ _ _ hj)
theorem returned_rank_bound (m j t : PTm n) (ht : Γ ⊢[PRAAx] lt t (RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    lt (fstT (rankRun m j t)) (RuntimePermutationWords.count m) :=
  lt_congr (returned_rank _ _ _).eqSymm (.eqRefl _) (.andE₁ (retained_transport _ _ _ ht hj))
theorem returned_rank_parity_flip (m j t : PTm n) (ht : Γ ⊢[PRAAx] lt t (RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    sndT (sndT (rankRun m j t)) ≐ monus one (RuntimePermutationWords.parity m (entry (RuntimePermutationWords.words m) t)) :=
  (returned_rank_parity _ _ _).eqTrans (retained_parity_flip _ _ _ ht hj)

/-! All dimensions, original codes, positions and retained ranks are bound
inside these ordinary PRA statements. The word-code involution retains
its original horizon guard independently of the permutation checker. -/
theorem actual_position_involution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (tau (var 0) (tau (var 0) (var 1)) ≐ var 1) := closeUniv 2 (tau_involution _ _)
theorem actual_tuple_preservation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RuntimePermutationWords.tuple (var 0) (var 1) ⟶ lt (succ (var 2)) (var 1) ⟶
      RuntimePermutationWords.tuple (swapTuple (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (.impI (tuple_preserved _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_swapped_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (succ (var 2)) (var 0) ⟶ lt (var 3) (var 0) ⟶
      RuntimePermutationWords.digit (var 0) (swapWord (var 0) (var 1) (var 2)) (var 3) ≐
        RuntimePermutationWords.digit (var 0) (var 1) (tau (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (swapped_digit _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_word_involution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (RuntimePermutationWords.horizon (var 0)) ⟶ lt (succ (var 2)) (var 0) ⟶
      swapWord (var 0) (swapWord (var 0) (var 1) (var 2)) (var 2) ≐ var 1) :=
  closeUniv 3 (.impI (.impI (word_involution _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_retained_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (RuntimePermutationWords.count (var 0)) ⟶ lt (succ (var 1)) (var 0) ⟶
      (lt (rankSwap (var 0) (var 1) (var 2)) (RuntimePermutationWords.count (var 0)) ⋏
        (entry (RuntimePermutationWords.words (var 0)) (rankSwap (var 0) (var 1) (var 2)) ≐
          swapWord (var 0) (entry (RuntimePermutationWords.words (var 0)) (var 2)) (var 1)))) :=
  closeUniv 3 (.impI (.impI (retained_transport _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rank_involution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (RuntimePermutationWords.count (var 0)) ⟶ lt (succ (var 1)) (var 0) ⟶
      rankSwap (var 0) (var 1) (rankSwap (var 0) (var 1) (var 2)) ≐ var 2) :=
  closeUniv 3 (.impI (.impI (rank_involution _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_adjacent_sum_closed (g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (succ (var 1)) (var 0) ⟶ ap2 (sumF (sumSwapBody g)) (var 0) (pairT (var 1) (var 2)) ≐ ap2 (sumF g) (var 0) (var 2)) :=
  closeUniv 3 (.impI (adjacent_sum _ _ _ _ Prf.hyp0))
theorem actual_inversion_balance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (succ (var 2)) (var 0) ⟶
      RuntimePermutationWords.inversions (var 0) (swapWord (var 0) (var 1) (var 2))+
        RuntimePermutationWords.inversionBit (var 0) (var 1) (var 2) (succ (var 2)) ≐
      RuntimePermutationWords.inversions (var 0) (var 1)+
        RuntimePermutationWords.inversionBit (var 0) (swapWord (var 0) (var 1) (var 2)) (var 2) (succ (var 2))) :=
  closeUniv 3 (.impI (inversion_balance _ _ _ Prf.hyp0))
theorem actual_inversion_odd_balance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (succ (var 2)) (var 0) ⟶ RuntimePermutationWords.permutation (var 0) (var 1) ⟶
      RuntimePermutationWords.inversions (var 0) (swapWord (var 0) (var 1) (var 2))+
        two*RuntimePermutationWords.inversionBit (var 0) (var 1) (var 2) (succ (var 2)) ≐
      RuntimePermutationWords.inversions (var 0) (var 1)+one) :=
  closeUniv 3 (.impI (.impI (inversion_odd_balance _ _ _ Prf.hyp1
    (adjacent_digits_different _ _ _ Prf.hyp0 Prf.hyp1))))
theorem actual_word_parity_flip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (succ (var 2)) (var 0) ⟶ RuntimePermutationWords.permutation (var 0) (var 1) ⟶
      RuntimePermutationWords.parity (var 0) (swapWord (var 0) (var 1) (var 2)) ≐
        monus one (RuntimePermutationWords.parity (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (parity_flip _ _ _ Prf.hyp1
    (adjacent_digits_different _ _ _ Prf.hyp0 Prf.hyp1))))
theorem actual_retained_parity_flip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (RuntimePermutationWords.count (var 0)) ⟶ lt (succ (var 1)) (var 0) ⟶
      RuntimePermutationWords.parity (var 0) (entry (RuntimePermutationWords.words (var 0)) (rankSwap (var 0) (var 1) (var 2))) ≐
        monus one (RuntimePermutationWords.parity (var 0) (entry (RuntimePermutationWords.words (var 0)) (var 2)))) :=
  closeUniv 3 (.impI (.impI (retained_parity_flip _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_retained_no_fixed_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (RuntimePermutationWords.count (var 0)) ⟶ lt (succ (var 1)) (var 0) ⟶
      neg (rankSwap (var 0) (var 1) (var 2) ≐ var 2)) :=
  closeUniv 3 (.impI (.impI (rank_no_fixed _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_word_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (wordRun (var 0) (var 1) (var 2) ≐ wordOutput (var 0) (var 1) (var 2)) :=
  closeUniv 3 (word_program_at _ _ _)
theorem actual_rank_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rankRun (var 0) (var 1) (var 2) ≐ rankOutput (var 0) (var 1) (var 2)) :=
  closeUniv 3 (rank_program_at _ _ _)
theorem actual_returned_retained_parity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (RuntimePermutationWords.count (var 0)) ⟶ lt (succ (var 1)) (var 0) ⟶
      sndT (sndT (rankRun (var 0) (var 1) (var 2))) ≐
        monus one (RuntimePermutationWords.parity (var 0) (entry (RuntimePermutationWords.words (var 0)) (var 2)))) :=
  closeUniv 3 (.impI (.impI (returned_rank_parity_flip _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.RuntimeAdjacentPermutationSwap
