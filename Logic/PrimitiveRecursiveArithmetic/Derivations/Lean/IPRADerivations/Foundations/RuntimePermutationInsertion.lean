import IPRADerivations.Foundations.RuntimePermutationDeletion

/-!
# Actual insertion of the largest numerical permutation label

Use the existing deletion reader to construct the larger word at an
arbitrary bounded position. The word has no repeated labels, and the
existing maximum-position scan and deleted-word program recover its inputs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.RuntimePermutationInsertion

open_ipra exports
open RuntimePermutationWords (digit range distinct tuple entriesEqual word encode horizon permutationBit)
open RuntimePermutationDeletion (recovered slot slot_before slot_after slot_bound slot_different after_index
  digits_different maximumPosition maximum_correct deletedWord deleted deleted_lookup deleted_range deleted_word_bound)
open RuntimeAdjacentPermutationSwap (digit_congr different_of_lt different_symm)
open MasterCertificate (entry sequence sequence_length sequence_decode)
open SequenceComposition (length)
open GuardedTotalization (sel sel_zero sel_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def compressed (p k : PTm n) : PTm n := sel (Signum.sg (monus p k)) k (pred k)
def data (m p d : PTm n) : PTm n := pairT m (pairT p d)
def body : PTm 2 := recovered (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def inserted (m p d : PTm n) : PTm n := sequence body (succ m) (data m p d)
def insertedWord (m p d : PTm n) : PTm n := encode (inserted m p d) (succ m)

ipra_subst compressed [sel, Signum.sg]

ipra_subst inserted [data]

ipra_subst insertedWord

theorem slot_congr {p q i j : PTm n} (hp : Γ ⊢[PRAAx] p ≐ q) (hi : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] slot p i ≐ slot q j := by
  ipra_congr (slot (var 0) (var 1) : PTm 2) with [hp, hi]

theorem compressed_congr (p : PTm n) {i j : PTm n} (h : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] compressed p i ≐ compressed p j := by
  ipra_congr (compressed (var 0) (var 1) : PTm 2) with [.eqRefl p, h]

theorem recovered_at (m p d k : PTm n) (h : Γ ⊢[PRAAx] k ≐ p) : Γ ⊢[PRAAx] recovered m p d k ≐ m :=
  sel_one (eqb_of_eq h)

theorem recovered_off (m p d k : PTm n) (h : Γ ⊢[PRAAx] neg (k ≐ p)) :
    Γ ⊢[PRAAx] recovered m p d k ≐ digit m d (compressed p k) := by
  have e := sel_zero (eqb_of_ne h) (a := m)
    (d := sel (Signum.sg (monus p k)) (digit m d k) (digit m d (pred k)))
  refine e.eqTrans (.orE (lt_or_le k p) ?_ ?_)
  · exact (sel_one (sg_lt Prf.hyp0)).eqTrans
      (digit_congr (.eqRefl m) (.eqRefl d) (sel_one (a := k) (d := pred k) (sg_lt Prf.hyp0)).eqSymm)
  · exact (sel_zero (sg_le Prf.hyp0)).eqTrans
      (digit_congr (.eqRefl m) (.eqRefl d) (sel_zero (a := k) (d := pred k) (sg_le Prf.hyp0)).eqSymm)

theorem inverse_after_skip (p i : PTm n) : Γ ⊢[PRAAx] compressed p (slot p i) ≐ i := by
  refine .orE (lt_or_le i p) ?_ ?_
  · exact (compressed_congr p (slot_before p i Prf.hyp0)).eqTrans (sel_one (sg_lt Prf.hyp0))
  · have above : le p i :: Γ ⊢[PRAAx] le p (succ i) := le_trans Prf.hyp0 (le_succ_self i)
    exact (compressed_congr p (slot_after p i Prf.hyp0)).eqTrans ((sel_zero (sg_le above)).eqTrans (pred_succ i))

theorem inverse_before_skip (m p k : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hk : Γ ⊢[PRAAx] lt k (succ m))
    (hne : Γ ⊢[PRAAx] neg (k ≐ p)) : Γ ⊢[PRAAx] lt (compressed p k) m ⋏ slot p (compressed p k) ≐ k := by
  refine .orE (Order.lt_or_gt_of_ne hne) ?_ ?_
  · have e : lt k p :: Γ ⊢[PRAAx] compressed p k ≐ k := sel_one (sg_lt Prf.hyp0)
    exact .andI (lt_congr e.eqSymm (.eqRefl _) (lt_of_lt_of_le Prf.hyp0 (Order.le_of_lt_succ hp.wk)))
      ((slot_congr (.eqRefl p) e).eqTrans (slot_before p k Prf.hyp0))
  · have coordinates := after_index m p k Prf.hyp0 hk.wk
    have e : lt p k :: Γ ⊢[PRAAx] compressed p k ≐ pred k := sel_zero (sg_le (le_of_lt Prf.hyp0))
    exact .andI (lt_congr e.eqSymm (.eqRefl _) coordinates.andE₁)
      ((slot_congr (.eqRefl p) e).eqTrans ((slot_after p _ coordinates.andE₂.andE₁).eqTrans coordinates.andE₂.andE₂))

theorem recovered_skip (m p d i : PTm n) : Γ ⊢[PRAAx] recovered m p d (slot p i) ≐ digit m d i :=
  (recovered_off m p d (slot p i) (slot_different p i)).eqTrans
    (digit_congr (.eqRefl m) (.eqRefl d) (inverse_after_skip p i))

theorem recovered_range (m p d k : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hk : Γ ⊢[PRAAx] lt k (succ m)) :
    Γ ⊢[PRAAx] lt (recovered m p d k) (succ m) := by
  refine .orE (eq_or_ne k p) ?_ ?_
  · exact lt_congr (recovered_at m p d k Prf.hyp0).eqSymm (.eqRefl _) (le_refl _)
  · have inverse := inverse_before_skip m p k hp.wk hk.wk (Prf.hyp0 : neg (k ≐ p) :: Γ ⊢[PRAAx] neg (k ≐ p))
    exact lt_congr (recovered_off m p d k Prf.hyp0).eqSymm (.eqRefl _)
      (lt_of_lt_of_le (RuntimePermutationWords.digit_bound _ _ _ inverse.andE₁) (le_succ_self m))

theorem recovered_different (m p d i j : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m))
    (hd : Γ ⊢[PRAAx] permutationBit m d ≐ one) (hi : Γ ⊢[PRAAx] lt i (succ m)) (hj : Γ ⊢[PRAAx] lt j (succ m))
    (hne : Γ ⊢[PRAAx] neg (i ≐ j)) : Γ ⊢[PRAAx] neg (recovered m p d i ≐ recovered m p d j) := by
  refine .orE (eq_or_ne i p) ?_ ?_
  · have ji : (i ≐ p) :: Γ ⊢[PRAAx] neg (j ≐ p) := .impI (.impE hne.wk.wk (Prf.hyp1.eqTrans Prf.hyp0.eqSymm))
    have inv := inverse_before_skip m p j hp.wk hj.wk ji
    have small := RuntimePermutationWords.digit_bound m d _ inv.andE₁
    have rb := lt_congr (recovered_off m p d j ji).eqSymm (recovered_at m p d i Prf.hyp0).eqSymm small
    exact different_symm (different_of_lt rb)
  · let Δ := neg (i ≐ p) :: Γ
    have ni : Δ ⊢[PRAAx] neg (i ≐ p) := Prf.hyp0
    have ii := inverse_before_skip m p i hp.wk hi.wk ni
    refine .orE (eq_or_ne j p) ?_ ?_
    · have small := RuntimePermutationWords.digit_bound (Γ := (j ≐ p) :: Δ) m d _ ii.andE₁.wk
      exact different_of_lt (lt_congr (recovered_off m p d i ni.wk).eqSymm (recovered_at m p d j Prf.hyp0).eqSymm small)
    · have nj : neg (j ≐ p) :: Δ ⊢[PRAAx] neg (j ≐ p) := Prf.hyp0
      have ij := inverse_before_skip m p j hp.wk.wk hj.wk.wk nj
      have no : neg (j ≐ p) :: Δ ⊢[PRAAx] neg (compressed p i ≐ compressed p j) :=
        .impI (.impE hne.wk.wk.wk (ii.andE₂.wk.wk.eqSymm.eqTrans
          ((slot_congr (.eqRefl p) Prf.hyp0).eqTrans ij.andE₂.wk)))
      have different := digits_different m d _ _ hd.wk.wk ii.andE₁.wk ij.andE₁ no
      exact .impI (.impE different.wk ((recovered_off m p d i ni.wk.wk).eqSymm.eqTrans
        (Prf.hyp0.eqTrans (recovered_off m p d j nj.wk))))

theorem body_at (m p d k : PTm n) : Γ ⊢[PRAAx] inst2 body k (data m p d) ≐ recovered m p d k := by
  let x := data m p d
  simpa only [x,body,inst2,RuntimePermutationDeletion.subst_recovered,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (recovered (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT x,fstT (sndT x),sndT (sndT x),k]) (σ' := ![m,p,d,k])
      (fun j => by
        fin_cases j
        · exact fst_pair m (pairT p d)
        · exact (congrFst (snd_pair m (pairT p d))).eqTrans (fst_pair p d)
        · exact (congrSnd (snd_pair m (pairT p d))).eqTrans (snd_pair p d)
        · exact .eqRefl _)

theorem inserted_length (m p d : PTm n) : Γ ⊢[PRAAx] length (inserted m p d) ≐ succ m := sequence_length _ _ _

theorem inserted_lookup (m p d k : PTm n) (hk : Γ ⊢[PRAAx] lt k (succ m)) :
    Γ ⊢[PRAAx] entry (inserted m p d) k ≐ recovered m p d k :=
  (sequence_decode body hk).eqTrans (body_at m p d k)

theorem inserted_range (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) : Γ ⊢[PRAAx] range (inserted m p d) (succ m) := by
  refine .allI (.impI ?_)
  let m' := Syn.shift m
  let p' := Syn.shift p
  let d' := Syn.shift d
  let Δ := lt (var 0) (succ m') :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] lt p' (succ m') := by simpa only [Δ,m',p',Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hp.shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 0) (succ m') := Prf.hyp0
  simpa only [Δ,m',p',d',Syn.shift,subst_inserted,ConciseIPRA.PTm.subst_succ] using
    lt_congr (inserted_lookup m' p' d' (var 0) hi).eqSymm (.eqRefl _) (recovered_range m' p' d' (var 0) hs hi)

theorem inserted_distinct (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m))
    (hd : Γ ⊢[PRAAx] permutationBit m d ≐ one) : Γ ⊢[PRAAx] distinct (inserted m p d) (succ m) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let m' := Syn.shift (Syn.shift m)
  let p' := Syn.shift (Syn.shift p)
  let d' := Syn.shift (Syn.shift d)
  let Δ := lt (var 0) (var 1) :: (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift).map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 1) (succ m') := by
    simpa only [Δ,m',List.map_cons,Fm.shift,subst_lt,Syn.subst_var,ConciseIPRA.PTm.subst_succ,Syn.shift,Fin.succ_zero_eq_one] using
      (Prf.hyp1 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift (succ m))).shift)
  have hj : Δ ⊢[PRAAx] lt (var 0) (succ m') := lt_of_lt_of_le Prf.hyp0 (le_of_lt hi)
  have hp' : Δ ⊢[PRAAx] lt p' (succ m') := by
    have copied : Δ ⊢[PRAAx] (lt p (succ m)).shift.shift := hp.shift.shift.wk.wk
    simpa only [m',p',Fm.shift,subst_lt,Syn.shift,ConciseIPRA.PTm.subst_succ] using copied
  have hd' : Δ ⊢[PRAAx] permutationBit m' d' ≐ one := by
    have copied : Δ ⊢[PRAAx] (permutationBit m d ≐ one).shift.shift := hd.shift.shift.wk.wk
    simpa only [m',d',Fm.shift,Fm.subst_eq,Syn.shift,RuntimePermutationWords.subst_permutationBit,
      ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using copied
  have diff := recovered_different m' p' d' (var 1) (var 0) hp' hd' hi hj
    (different_symm (different_of_lt (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (var 1))))
  have out : Δ ⊢[PRAAx] neg (entry (inserted m' p' d') (var 1) ≐ entry (inserted m' p' d') (var 0)) :=
    .impI (.impE diff.wk ((inserted_lookup m' p' d' (var 1) hi).wk.eqSymm.eqTrans
      (Prf.hyp0.eqTrans (inserted_lookup m' p' d' (var 0) hj).wk)))
  simpa only [Δ,m',p',d',List.map_cons,Fm.shift,subst_lt,RuntimePermutationWords.distinct,RuntimePermutationWords.distinctFrom,
    Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,subst_inserted,ConciseIPRA.PTm.subst_succ] using out

theorem inserted_tuple (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hd : Γ ⊢[PRAAx] permutationBit m d ≐ one) :
    Γ ⊢[PRAAx] tuple (inserted m p d) (succ m) :=
  .andI (inserted_length m p d) (.andI (inserted_range m p d hp) (inserted_distinct m p d hp hd))

theorem inserted_word_bound (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) :
    Γ ⊢[PRAAx] lt (insertedWord m p d) (horizon (succ m)) :=
  RuntimePermutationWords.encode_bound _ _ (inserted_range m p d hp)

theorem inserted_word_valid (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hd : Γ ⊢[PRAAx] permutationBit m d ≐ one) :
    Γ ⊢[PRAAx] permutationBit (succ m) (insertedWord m p d) ≐ one :=
  (RuntimePermutationWords.checker_reflection _ _).iffMpr (RuntimePermutationWords.encoded_tuple _ _ (inserted_tuple m p d hp hd))

theorem inserted_digit (m p d k : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hk : Γ ⊢[PRAAx] lt k (succ m)) :
    Γ ⊢[PRAAx] digit (succ m) (insertedWord m p d) k ≐ recovered m p d k :=
  (RuntimePermutationWords.encode_decode _ _ _ (inserted_range m p d hp) hk).eqTrans (inserted_lookup m p d k hk)

theorem inserted_maximum (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hd : Γ ⊢[PRAAx] permutationBit m d ≐ one) :
    Γ ⊢[PRAAx] maximumPosition m (insertedWord m p d) ≐ p := by
  let w := insertedWord m p d
  let q := maximumPosition m w
  have valid := inserted_word_valid m p d hp hd
  have max := maximum_correct m w (inserted_word_bound m p d hp) valid
  have atP := (inserted_digit m p d p hp hp).eqTrans (recovered_at m p d p (.eqRefl _))
  refine .orE (eq_or_ne q p) Prf.hyp0 ?_
  exact .botE _ (.impE (digits_different (succ m) w q p valid.wk max.andE₁.wk hp.wk Prf.hyp0)
    (max.andE₂.wk.eqTrans atP.wk.eqSymm))

theorem deleted_inserted_digit (m p d i : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hd : Γ ⊢[PRAAx] permutationBit m d ≐ one)
    (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx] digit m (deletedWord m (insertedWord m p d)) i ≐ digit m d i := by
  let w := insertedWord m p d
  have encoded := RuntimePermutationWords.encode_decode (deleted m w) m i
    (deleted_range m w (inserted_word_bound m p d hp) (inserted_word_valid m p d hp hd)) hi
  have shift := slot_congr (inserted_maximum m p d hp hd) (.eqRefl i)
  exact encoded.eqTrans ((deleted_lookup m w i hi).eqTrans
    ((digit_congr (.eqRefl _) (.eqRefl w) shift).eqTrans
      ((inserted_digit m p d (slot p i) hp (slot_bound m p i hi)).eqTrans (recovered_skip m p d i))))

theorem deleted_inserted_word (m p d : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hd : Γ ⊢[PRAAx] permutationBit m d ≐ one)
    (hb : Γ ⊢[PRAAx] lt d (horizon m)) : Γ ⊢[PRAAx] deletedWord m (insertedWord m p d) ≐ d := by
  let w := insertedWord m p d
  apply RuntimePermutationWords.word_unique m (deletedWord m w) d
    (deleted_word_bound m w (inserted_word_bound m p d hp) (inserted_word_valid m p d hp hd)) hb
  refine .allI (.impI ?_)
  let m' := Syn.shift m
  let p' := Syn.shift p
  let d' := Syn.shift d
  let Δ := lt (var 0) m' :: Γ.map Fm.shift
  have hp' : Δ ⊢[PRAAx] lt p' (succ m') := by simpa only [Δ,m',p',Fm.shift,subst_lt,Syn.shift,ConciseIPRA.PTm.subst_succ] using hp.shift.wk
  have hd' : Δ ⊢[PRAAx] permutationBit m' d' ≐ one := by
    simpa only [Δ,m',d',Fm.shift,Fm.subst_eq,Syn.shift,RuntimePermutationWords.subst_permutationBit,ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ] using hd.shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 0) m' := Prf.hyp0
  simpa only [Δ,m',p',d',w,Syn.shift,RuntimePermutationWords.subst_word,RuntimePermutationDeletion.subst_deletedWord,subst_insertedWord] using
    (RuntimePermutationWords.word_lookup _ _ _ hi).eqTrans
      ((deleted_inserted_digit m' p' d' (var 0) hp' hd' hi).eqTrans (RuntimePermutationWords.word_lookup _ _ _ hi).eqSymm)

theorem inserted_deleted_word (m w : PTm n) (hb : Γ ⊢[PRAAx] lt w (horizon (succ m)))
    (hw : Γ ⊢[PRAAx] permutationBit (succ m) w ≐ one) : Γ ⊢[PRAAx]
    insertedWord m (maximumPosition m w) (deletedWord m w) ≐ w := by
  let p := maximumPosition m w
  let d := deletedWord m w
  have hp : Γ ⊢[PRAAx] lt p (succ m) := (maximum_correct m w hb hw).andE₁
  have hd : Γ ⊢[PRAAx] permutationBit m d ≐ one := RuntimePermutationDeletion.deleted_word_valid m w hb hw
  exact RuntimePermutationDeletion.position_word_unique m (insertedWord m p d) w
    (inserted_word_bound m p d hp) hb (inserted_word_valid m p d hp hd) hw (inserted_maximum m p d hp hd)
    (deleted_inserted_word m p d hp hd (deleted_word_bound m w hb hw))

def insertF : PR 3 := PTm.toPR (insertedWord (var 0) (var 1) (var 2))
def run (m p d : PTm n) : PTm n := ap3 insertF m p d

theorem program_at (m p d : PTm n) : Γ ⊢[PRAAx] run m p d ≐ insertedWord m p d := by
  simpa [run,insertF,ap3] using toPR_eq (Γ := Γ) (insertedWord (var 0) (var 1) (var 2) : PTm 3) ![m,p,d]

theorem actual_inserted_permutation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (succ (var 0)) ⟶ permutationBit (var 0) (var 2) ≐ one ⟶
      lt (insertedWord (var 0) (var 1) (var 2)) (horizon (succ (var 0))) ⋏ permutationBit (succ (var 0)) (insertedWord (var 0) (var 1) (var 2)) ≐ one) :=
  closeUniv 3 (.impI (.impI (.andI (inserted_word_bound _ _ _ Prf.hyp1) (inserted_word_valid _ _ _ Prf.hyp1 Prf.hyp0))))

theorem actual_inserted_permutation_maximum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (succ (var 0)) ⟶ permutationBit (var 0) (var 2) ≐ one ⟶
      maximumPosition (var 0) (insertedWord (var 0) (var 1) (var 2)) ≐ var 1) :=
  closeUniv 3 (.impI (.impI (inserted_maximum _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_permutation_deletion_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (succ (var 0)) ⟶ permutationBit (var 0) (var 2) ≐ one ⟶ lt (var 2) (horizon (var 0)) ⟶
      deletedWord (var 0) (insertedWord (var 0) (var 1) (var 2)) ≐ var 2) :=
  closeUniv 3 (.impI (.impI (.impI (deleted_inserted_word _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_permutation_insertion_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (horizon (succ (var 0))) ⟶ permutationBit (succ (var 0)) (var 1) ≐ one ⟶
      insertedWord (var 0) (maximumPosition (var 0) (var 1)) (deletedWord (var 0) (var 1)) ≐ var 1) :=
  closeUniv 2 (.impI (.impI (inserted_deleted_word _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_permutation_insertion_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ insertedWord (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)

end LeanProofs.IPRA.Foundations.RuntimePermutationInsertion

export_ipra Foundations.RuntimePermutationInsertion (insertedWord)
