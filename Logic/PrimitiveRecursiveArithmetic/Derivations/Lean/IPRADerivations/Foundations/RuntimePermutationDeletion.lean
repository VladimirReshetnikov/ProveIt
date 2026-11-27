import IPRADerivations.Foundations.RuntimePermutationSums
import IPRADerivations.Foundations.RuntimeWordAppend
import IPRADerivations.Foundations.InjectionCount

/-!
# Actual deletion of the maximum digit of a numerical permutation word

The least maximum-digit position and the list obtained by skipping that
position are actual bounded programs. Original retained words, numerical
dimensions and both old word-code horizon guards are preserved. The
deleted word uses the existing numerical mixed-radix codec and retained
rank, rather than a host permutation or an assumed enumeration law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.RuntimePermutationDeletion

open_ipra exports
open RuntimePermutationWords (digit horizon permutationBit word encode tuple range distinct entriesEqual)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (m w : PTm n) : PTm n := RuntimePermutationWords.data m w
def maxTest : PTm 2 := eqb (sndT (var 1)) (digit (succ (sndT (var 1))) (fstT (var 1)) (var 0))
def maximumPosition (m w : PTm n) : PTm n := BoundedReflection.wit maxTest (succ m) (data m w)
def slot (p i : PTm n) : PTm n := sel (Signum.sg (monus p i)) i (succ i)
def deletedValue (m w i : PTm n) : PTm n := digit (succ m) w (slot (maximumPosition m w) i)
def deleteBody : PTm 2 := deletedValue (sndT (var 1)) (fstT (var 1)) (var 0)
def deleted (m w : PTm n) : PTm n := sequence deleteBody m (data m w)
def deletedWord (m w : PTm n) : PTm n := encode (deleted m w) m
def deletedRank (m w : PTm n) : PTm n := RuntimePermutationWords.position (deleted m w) m
ipra_subst data
ipra_subst maximumPosition [BoundedReflection.wit]
ipra_subst slot [sel, Signum.sg]
ipra_subst deletedValue
ipra_subst deleted
ipra_subst deletedWord
ipra_subst deletedRank [RuntimePermutationWords.position]

theorem max_test_at (m w i : PTm n) : Γ ⊢[PRAAx] inst2 maxTest i (data m w) ≐ eqb m (digit (succ m) w i) := by
  simp only [maxTest,inst2,subst_eqb,RuntimePermutationWords.subst_digit,subst_fstT,subst_sndT,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact AnalyticNumberTheory.Euler.congrEqb (snd_pair _ _)
    (RuntimeAdjacentPermutationSwap.digit_congr (congrSucc (snd_pair _ _)) (fst_pair _ _) (.eqRefl _))
theorem maximum_sum (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx] ap2 (sumF maxTest) (succ m) (data m w) ≐ one := by
  have terms : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ m)) ⟶
      inst2 maxTest (var 0) (Syn.shift (data m w)) ≐ inst2 (RuntimePermutationSums.reader (eqb (var 1) (var 0) : PTm 2))
        (var 0) (Syn.shift (RuntimePermutationSums.data (succ m) w m))) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift
    have rd : Δ ⊢[PRAAx] inst2 (RuntimePermutationSums.reader (eqb (var 1) (var 0) : PTm 2)) (var 0)
        (RuntimePermutationSums.data (succ (Syn.shift m)) (Syn.shift w) (Syn.shift m)) ≐ eqb (Syn.shift m) (digit (succ (Syn.shift m)) (Syn.shift w) (var 0)) := by
      simpa only [RuntimePermutationSums.read,inst2,subst_eqb,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
        RuntimePermutationSums.reader_at (Γ := Δ) (eqb (var 1) (var 0) : PTm 2) (succ (Syn.shift m)) (Syn.shift w) (Syn.shift m) (var 0)
    have e := (max_test_at (Γ := Δ) (Syn.shift m) (Syn.shift w) (var 0)).eqTrans rd.eqSymm
    simpa only [Δ,Syn.shift,subst_data,RuntimePermutationSums.subst_data,ConciseIPRA.PTm.subst_succ,
      RuntimePermutationSums.read,inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using e
  exact (sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((RuntimePermutationSums.permutation_sum (eqb (var 1) (var 0) : PTm 2) (succ m) w m hw hp).eqTrans
      (InjectionCount.delta_one (le_refl (succ m))))
theorem maximum_correct (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx]
    lt (maximumPosition m w) (succ m) ⋏ digit (succ m) w (maximumPosition m w) ≐ m := by
  have bit : Γ ⊢[PRAAx] BoundedReflection.exB maxTest (succ m) (data m w) ≐ one := by
    refine .orE (BoundedReflection.ex_cases maxTest (succ m) (data m w)) ?_ Prf.hyp0
    have no : (BoundedReflection.exB maxTest (succ m) (data m w) ≐ zero) :: Γ ⊢[PRAAx]
        ap2 (sumF maxTest) (succ m) (data m w) ≐ zero := by
      apply sum_zero_of_bounded
      refine .allI (.impI ?_)
      have hs : ((BoundedReflection.exB maxTest (succ m) (data m w) ≐ zero) :: Γ).map Fm.shift ⊢[PRAAx]
          BoundedReflection.exB maxTest (succ (Syn.shift m)) (data (Syn.shift m) (Syn.shift w)) ≐ zero := by
        simpa [Fm.shift,Syn.shift] using (Prf.hyp0 : (BoundedReflection.exB maxTest (succ m) (data m w) ≐ zero) :: Γ ⊢[PRAAx] _).shift
      simpa only [Syn.shift,subst_data,ConciseIPRA.PTm.subst_succ] using BoundedReflection.ex_none (f := maxTest) hs.wk Prf.hyp0
    exact .botE _ (succ_ne_zero ((maximum_sum m w hw hp).wk.eqSymm.eqTrans no))
  have found := BoundedReflection.ex_elim (f := maxTest) bit
  have hit := AnalyticNumberTheory.Valuation.eq_of_eqb_ne (by
    exact .impI (.impE (Prf.andE₂ found).wk ((max_test_at m w (maximumPosition m w)).wk.eqTrans Prf.hyp0)))
  exact .andI (.andE₁ found) hit.eqSymm

theorem slot_before (p i : PTm n) (hi : Γ ⊢[PRAAx] lt i p) : Γ ⊢[PRAAx] slot p i ≐ i :=
  sel_one (AnalyticNumberTheory.Totatives.sg_lt hi)
theorem slot_after (p i : PTm n) (hi : Γ ⊢[PRAAx] le p i) : Γ ⊢[PRAAx] slot p i ≐ succ i :=
  sel_zero (AnalyticNumberTheory.Totatives.sg_le hi)
theorem slot_bound (m p i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx] lt (slot p i) (succ m) := by
  refine .orE (lt_or_le i p) ?_ ?_
  · exact lt_congr (slot_before _ _ Prf.hyp0).eqSymm (.eqRefl _) (lt_of_lt_of_le hi.wk (le_succ_self m))
  · exact lt_congr (slot_after _ _ Prf.hyp0).eqSymm (.eqRefl _) ((succ_monus_succ (succ i) m).eqTrans hi.wk)
theorem slot_different (p i : PTm n) : Γ ⊢[PRAAx] neg (slot p i ≐ p) := by
  refine .orE (lt_or_le i p) ?_ ?_
  · exact .impI (lt_irrefl p _ (lt_congr ((slot_before p i Prf.hyp1).eqSymm.eqTrans Prf.hyp0) (.eqRefl _) Prf.hyp1))
  · exact .impI (not_succ_le_self i _ (le_congr (Prf.hyp0.eqSymm.eqTrans (slot_after _ _ Prf.hyp1)) (.eqRefl _) Prf.hyp1))
theorem slot_strict (p i j : PTm n) (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx] lt (slot p i) (slot p j) := by
  refine .orE (lt_or_le j p) ?_ ?_
  · exact lt_congr (slot_before _ _ (lt_of_lt_of_le hij.wk (le_of_lt Prf.hyp0))).eqSymm (slot_before _ _ Prf.hyp0).eqSymm hij.wk
  · refine .orE (lt_or_le i p) ?_ ?_
    · exact lt_congr (slot_before _ _ Prf.hyp0).eqSymm (slot_after _ _ Prf.hyp1).eqSymm (lt_of_lt_of_le hij.wk.wk (le_succ_self j))
    · exact lt_congr (slot_after _ _ Prf.hyp0).eqSymm (slot_after _ _ Prf.hyp1).eqSymm ((succ_monus_succ (succ i) j).eqTrans hij.wk.wk)

theorem delete_body_at (m w i : PTm n) : Γ ⊢[PRAAx] inst2 deleteBody i (data m w) ≐ deletedValue m w i := by
  simp only [deleteBody,inst2,subst_deletedValue,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  ipra_congr (deletedValue (var 0) (var 1) (var 2) : PTm 3) with
    [(show _ ⊢[PRAAx] sndT (data m w) ≐ m from snd_pair _ _),
      (show _ ⊢[PRAAx] fstT (data m w) ≐ w from fst_pair _ _), .eqRefl i]
theorem deleted_length (m w : PTm n) : Γ ⊢[PRAAx] length (deleted m w) ≐ m := sequence_length _ _ _
theorem deleted_lookup (m w i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    entry (deleted m w) i ≐ digit (succ m) w (slot (maximumPosition m w) i) := (sequence_decode deleteBody hi).eqTrans (delete_body_at _ _ _)

theorem digits_different (m w i j : PTm n) (hp : Γ ⊢[PRAAx] permutationBit m w ≐ one)
    (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt j m) (hne : Γ ⊢[PRAAx] neg (i ≐ j)) : Γ ⊢[PRAAx]
    neg (digit m w i ≐ digit m w j) := by
  have no := RuntimeAdjacentPermutationSwap.distinct_entries (word m w) m i j
    (Prf.andE₂ (Prf.andE₂ ((RuntimePermutationWords.checker_reflection m w).iffMp hp))) hi hj hne
  exact .impI (.impE no.wk ((RuntimePermutationWords.word_lookup _ _ _ hi).wk.eqTrans
    (Prf.hyp0.eqTrans (RuntimePermutationWords.word_lookup _ _ _ hj).wk.eqSymm)))
theorem deleted_value_bound (m w i : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    lt (deletedValue m w i) m := by
  have max := maximum_correct m w hw hp
  have bound := RuntimePermutationWords.digit_bound (succ m) w (slot (maximumPosition m w) i) (slot_bound _ _ _ hi)
  have small := Order.le_of_lt_succ bound
  have different := digits_different (succ m) w (slot (maximumPosition m w) i) (maximumPosition m w)
    hp (slot_bound _ _ _ hi) (Prf.andE₁ max) (slot_different _ _)
  exact Order.lt_of_le_of_ne small
    (.impI (.impE different.wk (Prf.hyp0.eqTrans (Prf.andE₂ max).wk.eqSymm)))
theorem deleted_range (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx] range (deleted m w) m := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift w) (horizon (succ (Syn.shift m))) := by simpa [Fm.shift,Syn.shift] using hw.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] permutationBit (succ (Syn.shift m)) (Syn.shift w) ≐ one := by simpa [Fm.shift,Syn.shift] using hp.shift
  refine .allI (.impI ?_)
  have e := lt_congr (deleted_lookup (Syn.shift m) (Syn.shift w) (var 0) Prf.hyp0).eqSymm (.eqRefl _)
    (deleted_value_bound _ _ _ hs.wk ps.wk Prf.hyp0)
  simpa only [Syn.shift,subst_deleted] using e
theorem deleted_distinct (m w : PTm n) (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx] distinct (deleted m w) m := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (var 1) :: (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift).map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.subst_var,Syn.shift,Fin.succ_zero_eq_one] using
      (Prf.hyp1 : Δ ⊢[PRAAx] Fm.shift (lt (var 0) (Syn.shift m)))
  have hj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift m)) := lt_of_lt_of_le Prf.hyp0 (le_of_lt hi)
  have ps : Δ ⊢[PRAAx] permutationBit (succ (Syn.shift (Syn.shift m))) (Syn.shift (Syn.shift w)) ≐ one := by
    have copied : Δ ⊢[PRAAx] (permutationBit (succ m) w ≐ one).shift.shift := hp.shift.shift.wk.wk
    simpa only [Fm.shift,Fm.subst_eq,Syn.shift,RuntimePermutationWords.subst_permutationBit,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using copied
  let p := maximumPosition (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift w))
  have no := digits_different (succ (Syn.shift (Syn.shift m))) (Syn.shift (Syn.shift w)) (slot p (var 1)) (slot p (var 0))
    ps (slot_bound _ p _ hi) (slot_bound _ p _ hj)
    (RuntimeAdjacentPermutationSwap.different_symm (RuntimeAdjacentPermutationSwap.different_of_lt (slot_strict p _ _ Prf.hyp0)))
  have out : Δ ⊢[PRAAx] neg (entry (deleted (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift w))) (var 1) ≐
      entry (deleted (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift w))) (var 0)) :=
    .impI (.impE no.wk ((deleted_lookup _ _ _ hi).wk.eqSymm.eqTrans
      (Prf.hyp0.eqTrans (deleted_lookup _ _ _ hj).wk)))
  simpa only [Δ,List.map_cons,Fm.shift,subst_lt,RuntimePermutationWords.distinct,RuntimePermutationWords.distinctFrom,Syn.shift,Syn.subst_var,
    Fin.succ_zero_eq_one,subst_deleted] using out
theorem deleted_tuple (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx] tuple (deleted m w) m :=
  .andI (deleted_length m w) (.andI (deleted_range m w hw hp) (deleted_distinct m w hp))
theorem deleted_word_bound (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx] lt (deletedWord m w) (horizon m) :=
  RuntimePermutationWords.encode_bound _ _ (deleted_range m w hw hp)
theorem deleted_word_valid (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx] permutationBit m (deletedWord m w) ≐ one :=
  (RuntimePermutationWords.checker_reflection _ _).iffMpr (RuntimePermutationWords.encoded_tuple _ _ (deleted_tuple m w hw hp))
theorem deleted_rank_correct (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx]
    lt (deletedRank m w) (RuntimePermutationWords.count m) ⋏ entry (RuntimePermutationWords.words m) (deletedRank m w) ≐ deletedWord m w :=
  RuntimePermutationWords.listed _ _ (deleted_tuple m w hw hp)

theorem after_index (m p k : PTm n) (hp : Γ ⊢[PRAAx] lt p k) (hk : Γ ⊢[PRAAx] lt k (succ m)) : Γ ⊢[PRAAx]
    lt (pred k) m ⋏ (le p (pred k) ⋏ succ (pred k) ≐ k) := by
  have form := RuntimeWordAppend.positive_form k (lt_of_le_of_lt (zero_le p) hp)
  have km : Γ ⊢[PRAAx] le k m := (succ_monus_succ k m).eqSymm.eqTrans hk
  have pk : Γ ⊢[PRAAx] le p (pred k) :=
    (succ_monus_succ p (pred k)).eqSymm.eqTrans (le_congr (.eqRefl _) form hp)
  exact .andI (le_congr form (.eqRefl _) km) (.andI pk form.eqSymm)
def recovered (m p d k : PTm n) : PTm n := sel (eqb k p) m
  (sel (Signum.sg (monus p k)) (digit m d k) (digit m d (pred k)))
ipra_subst recovered [sel, Signum.sg]
theorem recovered_congr {m p p' d d' k : PTm n} (hp : Γ ⊢[PRAAx] p ≐ p') (hd : Γ ⊢[PRAAx] d ≐ d') : Γ ⊢[PRAAx]
    recovered m p d k ≐ recovered m p' d' k := by
  ipra_congr (recovered (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl m, hp, hd, .eqRefl k]
theorem recovered_correct (m w k : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) (hk : Γ ⊢[PRAAx] lt k (succ m)) : Γ ⊢[PRAAx]
    recovered m (maximumPosition m w) (deletedWord m w) k ≐ digit (succ m) w k := by
  have mx := maximum_correct m w hw hp
  have dr := deleted_range m w hw hp
  refine .orE (eq_or_ne k (maximumPosition m w)) ?_ ?_
  · exact (sel_one (eqb_of_eq Prf.hyp0)).eqTrans
      ((Prf.andE₂ mx).wk.eqSymm.eqTrans (RuntimeAdjacentPermutationSwap.digit_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))
  · have first := sel_zero (eqb_of_ne (Γ := neg (k ≐ maximumPosition m w) :: Γ) Prf.hyp0)
      (a := m) (d := sel (Signum.sg (monus (maximumPosition m w) k)) (digit m (deletedWord m w) k) (digit m (deletedWord m w) (pred k)))
    refine first.eqTrans (.orE (Order.lt_or_gt_of_ne Prf.hyp0) ?_ ?_)
    · have km : lt k (maximumPosition m w) :: neg (k ≐ maximumPosition m w) :: Γ ⊢[PRAAx] lt k m :=
        lt_of_lt_of_le Prf.hyp0 (Order.le_of_lt_succ (Prf.andE₁ mx).wk.wk)
      exact (sel_one (AnalyticNumberTheory.Totatives.sg_lt Prf.hyp0)).eqTrans
        ((RuntimePermutationWords.encode_decode _ _ _ dr.wk.wk km).eqTrans
          ((deleted_lookup _ _ _ km).eqTrans (RuntimeAdjacentPermutationSwap.digit_congr (.eqRefl _) (.eqRefl _) (slot_before _ _ Prf.hyp0))))
    · have indices := after_index m (maximumPosition m w) k
        (Prf.hyp0 (Γ := neg (k ≐ maximumPosition m w) :: Γ)) hk.wk.wk
      exact (sel_zero (AnalyticNumberTheory.Totatives.sg_le (le_of_lt Prf.hyp0))).eqTrans
        ((RuntimePermutationWords.encode_decode _ _ _ dr.wk.wk (Prf.andE₁ indices)).eqTrans
          ((deleted_lookup _ _ _ (Prf.andE₁ indices)).eqTrans
            (RuntimeAdjacentPermutationSwap.digit_congr (.eqRefl _) (.eqRefl _)
              ((slot_after _ _ (Prf.andE₁ (Prf.andE₂ indices))).eqTrans (Prf.andE₂ (Prf.andE₂ indices))))))

theorem position_word_unique (m w v : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hv : Γ ⊢[PRAAx] lt v (horizon (succ m))) (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one)
    (hq : Γ ⊢[PRAAx] permutationBit (succ m) v ≐ one) (he : Γ ⊢[PRAAx] maximumPosition m w ≐ maximumPosition m v)
    (hd : Γ ⊢[PRAAx] deletedWord m w ≐ deletedWord m v) : Γ ⊢[PRAAx] w ≐ v := by
  refine RuntimePermutationWords.word_unique _ _ _ hw hv (.allI (.impI ?_))
  let Δ := lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift
  have ws : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift w) (horizon (succ (Syn.shift m))) := by simpa [Fm.shift,Syn.shift] using hw.shift
  have vs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift v) (horizon (succ (Syn.shift m))) := by simpa [Fm.shift,Syn.shift] using hv.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] permutationBit (succ (Syn.shift m)) (Syn.shift w) ≐ one := by simpa [Fm.shift,Syn.shift] using hp.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] permutationBit (succ (Syn.shift m)) (Syn.shift v) ≐ one := by simpa [Fm.shift,Syn.shift] using hq.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] maximumPosition (Syn.shift m) (Syn.shift w) ≐ maximumPosition (Syn.shift m) (Syn.shift v) := by simpa [Fm.shift,Syn.shift] using he.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] deletedWord (Syn.shift m) (Syn.shift w) ≐ deletedWord (Syn.shift m) (Syn.shift v) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have e := (RuntimePermutationWords.word_lookup (Γ := Δ) (succ (Syn.shift m)) (Syn.shift w) (var 0) Prf.hyp0).eqTrans
    ((recovered_correct _ _ _ ws.wk ps.wk Prf.hyp0).eqSymm.eqTrans
      ((recovered_congr es.wk ds.wk).eqTrans
        ((recovered_correct _ _ _ vs.wk qs.wk Prf.hyp0).eqTrans (RuntimePermutationWords.word_lookup _ _ _ Prf.hyp0).eqSymm)))
  simpa only [Δ,RuntimePermutationWords.subst_word,Syn.shift,ConciseIPRA.PTm.subst_succ] using e
theorem position_rank_unique (m w v : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hv : Γ ⊢[PRAAx] lt v (horizon (succ m))) (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one)
    (hq : Γ ⊢[PRAAx] permutationBit (succ m) v ≐ one) (he : Γ ⊢[PRAAx] maximumPosition m w ≐ maximumPosition m v)
    (hd : Γ ⊢[PRAAx] deletedRank m w ≐ deletedRank m v) : Γ ⊢[PRAAx] w ≐ v :=
  position_word_unique m w v hw hv hp hq he
    ((Prf.andE₂ (deleted_rank_correct m w hw hp)).eqSymm.eqTrans
      ((entry_congr (.eqRefl _) hd).eqTrans (Prf.andE₂ (deleted_rank_correct m v hv hq))))

def packed (m w : PTm n) : PTm n := deletedRank m w+maximumPosition m w*RuntimePermutationWords.count m
ipra_subst packed
theorem packed_bound (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx]
    lt (packed m w) (RuntimePermutationWords.count m*succ m) :=
  MixedRadixExpansion.append_interval (Prf.andE₁ (deleted_rank_correct m w hw hp)) (Prf.andE₁ (maximum_correct m w hw hp))
theorem packed_coordinates (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx]
    quo (packed m w) (RuntimePermutationWords.count m) ≐ maximumPosition m w ⋏
      rem (packed m w) (RuntimePermutationWords.count m) ≐ deletedRank m w :=
  RuntimeWordAppend.divide_unique _ _ _ _ (RuntimePermutationWords.words_nonempty m)
    (by unfold packed; ipra_ring) (Prf.andE₁ (deleted_rank_correct m w hw hp))
theorem packed_unique (m w v : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hv : Γ ⊢[PRAAx] lt v (horizon (succ m))) (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one)
    (hq : Γ ⊢[PRAAx] permutationBit (succ m) v ≐ one) (he : Γ ⊢[PRAAx] packed m w ≐ packed m v) : Γ ⊢[PRAAx] w ≐ v := by
  have left := packed_coordinates m w hw hp
  have right := packed_coordinates m v hv hq
  exact position_rank_unique m w v hw hv hp hq
    ((Prf.andE₁ left).eqSymm.eqTrans ((congrAp2 quoF he (.eqRefl _)).eqTrans (Prf.andE₁ right)))
    ((Prf.andE₂ left).eqSymm.eqTrans ((congrAp2 remF he (.eqRefl _)).eqTrans (Prf.andE₂ right)))

def output (m w : PTm n) : PTm n := pairT (maximumPosition m w) (pairT (deleted m w)
  (pairT (deletedWord m w) (pairT (deletedRank m w) (packed m w))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (m w : PTm n) : PTm n := ap2 outputF m w
def fields (p : PTm n) : Fin 5 → PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),
  fstT (sndT (sndT (sndT p))),sndT (sndT (sndT (sndT p)))]
ipra_subst output
ipra_subst run
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 5) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (m w : PTm n) : Γ ⊢[PRAAx] run m w ≐ output m w := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![m,w]
theorem returned_fields (m w : PTm n) (i : Fin 5) : Γ ⊢[PRAAx] fields (run m w) i ≐
    ![maximumPosition m w,deleted m w,deletedWord m w,deletedRank m w,packed m w] i :=
  pairVectorField_eq 4 _ (program_at m w) i
theorem returned_packed_bound (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hp : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx]
    lt (fields (run m w) 4) (RuntimePermutationWords.count m*succ m) :=
  lt_congr (returned_fields m w 4).eqSymm (.eqRefl _) (packed_bound m w hw hp)

theorem actual_maximum_correct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (horizon (succ (var 0))) ⟶ permutationBit (succ (var 0)) (var 1) ≐ one ⟶
      lt (maximumPosition (var 0) (var 1)) (succ (var 0)) ⋏ digit (succ (var 0)) (var 1) (maximumPosition (var 0) (var 1)) ≐ var 0) :=
  closeUniv 2 (.impI (.impI (maximum_correct _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_deleted_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (deleted (var 0) (var 1)) ≐ var 0) := closeUniv 2 (deleted_length _ _)
theorem actual_deleted_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 0) ⟶ entry (deleted (var 0) (var 1)) (var 2) ≐
      digit (succ (var 0)) (var 1) (slot (maximumPosition (var 0) (var 1)) (var 2))) := closeUniv 3 (.impI (deleted_lookup _ _ _ Prf.hyp0))
theorem actual_deleted_tuple_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (horizon (succ (var 0))) ⟶ permutationBit (succ (var 0)) (var 1) ≐ one ⟶ tuple (deleted (var 0) (var 1)) (var 0)) :=
  closeUniv 2 (.impI (.impI (deleted_tuple _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_deleted_rank_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (horizon (succ (var 0))) ⟶ permutationBit (succ (var 0)) (var 1) ≐ one ⟶
      lt (deletedRank (var 0) (var 1)) (RuntimePermutationWords.count (var 0)) ⋏
        entry (RuntimePermutationWords.words (var 0)) (deletedRank (var 0) (var 1)) ≐ deletedWord (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (deleted_rank_correct _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_deleted_recovery_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (horizon (succ (var 0))) ⟶ permutationBit (succ (var 0)) (var 1) ≐ one ⟶ lt (var 2) (succ (var 0)) ⟶
      recovered (var 0) (maximumPosition (var 0) (var 1)) (deletedWord (var 0) (var 1)) (var 2) ≐ digit (succ (var 0)) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (recovered_correct _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_packed_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (horizon (succ (var 0))) ⟶ permutationBit (succ (var 0)) (var 1) ≐ one ⟶
      lt (packed (var 0) (var 1)) (RuntimePermutationWords.count (var 0)*succ (var 0))) :=
  closeUniv 2 (.impI (.impI (packed_bound _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_packed_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (horizon (succ (var 0))) ⟶ lt (var 2) (horizon (succ (var 0))) ⟶
      permutationBit (succ (var 0)) (var 1) ≐ one ⟶ permutationBit (succ (var 0)) (var 2) ≐ one ⟶
        packed (var 0) (var 1) ≐ packed (var 0) (var 2) ⟶ var 1 ≐ var 2) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.impI (packed_unique _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_deletion_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_packed_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (horizon (succ (var 0))) ⟶ permutationBit (succ (var 0)) (var 1) ≐ one ⟶
      lt (fields (run (var 0) (var 1)) 4) (RuntimePermutationWords.count (var 0)*succ (var 0))) :=
  closeUniv 2 (.impI (.impI (returned_packed_bound _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.RuntimePermutationDeletion

export_ipra Foundations.RuntimePermutationDeletion (maximumPosition slot_after slot_before slot_bound)
