import IPRADerivations.Analysis.RationalMinorFreeColumn
import IPRADerivations.Analysis.RationalFiniteSpanCover
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CommonLemmas

/-!
# Extending a selected minor by an actual new row or column

Repack the original mask digits in the same numerical binary encoding,
with the requested digit replaced by one. The exact decoder supplies all
old digits at other positions. When the requested digit was zero, the
actual filtered count increases by one and the new index is retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalMinorMaskExtension

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus)
open RationalSubtupleSpan (bit bitBody bit_body_at)
open RationalSelectedMinors (count indices index index_bound index_selected selected_listed)
open RationalMinorFreeColumn (bit_cases)
open RationalArithmetic (select select_zero select_one)
open LeanProofs.IPRA.Foundations.BoundedReflection (sgB inst2_sgB)
open LeanProofs.IPRA.Foundations.MixedRadix (Cd Pl dP)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def insertedBit (M c i : PTm n) : PTm n := select (eqb i c) (bit M i) one
def digitBody : PTm 2 := insertedBit (sndT (var 1)) (fstT (var 1)) (var 0)
def insert (N M c : PTm n) : PTm n := Cd (two : PTm 2) digitBody N (pairT c M)

@[simp] theorem subst_insertedBit {k : ℕ} (σ : Fin n → PTm k) (M c i : PTm n) :
    Syn.subst σ (insertedBit M c i) = insertedBit (Syn.subst σ M) (Syn.subst σ c) (Syn.subst σ i) := by
  simp [insertedBit,one]
@[simp] theorem subst_insert {k : ℕ} (σ : Fin n → PTm k) (N M c : PTm n) :
    Syn.subst σ (insert N M c) = insert (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ c) := by simp [insert]

theorem digit_body_at (M c i : PTm n) : Γ ⊢[PRAAx] inst2 digitBody i (pairT c M) ≐ insertedBit M c i := by
  ipra_congr (insertedBit (var 0) (var 1) (var 2) : PTm 3) with
    [snd_pair _ _, fst_pair _ _, .eqRefl i] using [digitBody, inst2]

theorem inserted_bit_hit (M c i : PTm n) (h : Γ ⊢[PRAAx] i ≐ c) : Γ ⊢[PRAAx] insertedBit M c i ≐ one :=
  select_one _ _ _ (eqb_of_eq h)

theorem inserted_bit_miss (M c i : PTm n) (h : Γ ⊢[PRAAx] neg (i ≐ c)) : Γ ⊢[PRAAx] insertedBit M c i ≐ bit M i :=
  select_zero _ _ _ (eqb_of_ne h)

theorem inserted_bit_bound (M c i : PTm n) : Γ ⊢[PRAAx] lt (insertedBit M c i) two := by
  refine .orE (eq_or_ne i c) ?_ ?_
  · exact lt_congr (inserted_bit_hit M c i Prf.hyp0).eqSymm (.eqRefl _) (le_refl two)
  · refine .orE (bit_cases i M) ?_ ?_
    · exact lt_congr ((inserted_bit_miss M c i Prf.hyp1).eqTrans Prf.hyp0).eqSymm (.eqRefl _) (le_succ_self one)
    · exact lt_congr ((inserted_bit_miss M c i Prf.hyp1).eqTrans Prf.hyp0).eqSymm (.eqRefl _) (le_refl two)

theorem digit_bounds (N M c : PTm n) : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift N) ⟶
      lt (inst2 digitBody (var 0) (Syn.shift (pairT c M))) (inst2 (two : PTm 2) (var 0) (Syn.shift (pairT c M)))) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_pairT,inst2,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    lt_congr (digit_body_at (Syn.shift M) (Syn.shift c) (var 0)).eqSymm (.eqRefl _)
      (inserted_bit_bound (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift M) (Syn.shift c) (var 0))

theorem insert_bound (N M c : PTm n) : Γ ⊢[PRAAx] lt (insert N M c) (pw two N) :=
  lt_congr (.eqRefl _) (RationalFiniteSpanCover.places N (pairT c M))
    (Foundations.MixedRadix.code_lt _ _ _ _ (digit_bounds N M c))

theorem insert_digit (N M c i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bit (insert N M c) i ≐ insertedBit M c i := by
  let t := monus N (succ i)
  have span : Γ ⊢[PRAAx] succ i+t ≐ N := (eq_add_of_le hi).eqSymm
  have decoded := Foundations.MixedRadix.decode (digit_bounds (Γ := Γ) (succ i+t) M c)
  have twoAt : inst2 (two : PTm 2) i (pairT c M) = (two : PTm n) := by simp [inst2,two,one]
  rw [twoAt] at decoded
  have codeEq : Γ ⊢[PRAAx] Cd (two : PTm 2) digitBody (succ i+t) (pairT c M) ≐ insert N M c :=
    congrAp2 (sumF (dP (two : PTm 2) digitBody)) span (.eqRefl _)
  exact (congrAp2 remF (congrAp2 quoF codeEq (RationalFiniteSpanCover.places i (pairT c M))) (.eqRefl two)).eqSymm.eqTrans
    (decoded.eqTrans (digit_body_at M c i))

theorem new_bit (N M c : PTm n) (h : Γ ⊢[PRAAx] lt c N) : Γ ⊢[PRAAx] bit (insert N M c) c ≐ one :=
  (insert_digit _ _ _ _ h).eqTrans (inserted_bit_hit _ _ _ (.eqRefl _))

theorem old_bit (N M c i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) (hne : Γ ⊢[PRAAx] neg (i ≐ c)) :
    Γ ⊢[PRAAx] bit (insert N M c) i ≐ bit M i :=
  (insert_digit _ _ _ _ hi).eqTrans (inserted_bit_miss _ _ _ hne)

private alias sg_congr := Common.congrSg

theorem indicator_changes (N M c i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) (hc : Γ ⊢[PRAAx] bit M c ≐ zero) :
    Γ ⊢[PRAAx] Signum.sg (bit (insert N M c) i) ≐ Signum.sg (bit M i) + eqb c i := by
  refine .orE (eq_or_ne i c) ?_ ?_
  · have e : (i ≐ c) :: Γ ⊢[PRAAx] bit M i ≐ bit M c := by
      ipra_congr (bit (var 0) (var 1) : PTm 2) with [.eqRefl M, Prf.hyp0]
    have b := e.eqTrans hc.wk
    exact ((sg_congr ((insert_digit N M c i hi.wk).eqTrans (inserted_bit_hit M c i Prf.hyp0))).eqTrans
      (Signum.sg_succ zero)).eqTrans
      (((congrAdd ((sg_congr b).eqTrans Signum.sg_zero) (eqb_of_eq Prf.hyp0.eqSymm)).eqTrans (zero_add one)).eqSymm)
  · exact (sg_congr (old_bit N M c i hi.wk Prf.hyp0)).eqTrans
      (((congrAdd (.eqRefl _) (eqb_of_ne (.impI (.impE Prf.hyp1 Prf.hyp0.eqSymm)))).eqTrans (add_zero _)).eqSymm)

def previousBody : PTm 2 := Signum.sg (bit (sndT (var 1)) (var 0))
def deltaBody : PTm 2 := dB (one : PTm 2)

theorem previous_body_at (M c i : PTm n) : Γ ⊢[PRAAx] inst2 previousBody i (pairT c M) ≐ Signum.sg (bit M i) := by
  have e := congrInst2 bitBody (.eqRefl i) (snd_pair (Γ := Γ) c M)
  rw [bit_body_at,bit_body_at] at e
  simpa [previousBody,inst2,Signum.sg] using sg_congr e

theorem delta_body_at (M c i : PTm n) : Γ ⊢[PRAAx] inst2 deltaBody i (pairT c M) ≐ eqb c i := by
  have e : inst2 (one : PTm 2) i (sndT (pairT c M)) = (one : PTm n) := by simp [inst2,one]
  rw [deltaBody,inst2_dB,e]
  have e' := congrInst2 (eqb (var 1) (var 0) : PTm 2) (.eqRefl i) (fst_pair (Γ := Γ) c M)
  simp only [inst2,subst_eqb,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] at e'
  exact (congrMul e' (.eqRefl _)).eqTrans (by ipra_ring)

theorem previous_sum (N M c : PTm n) : Γ ⊢[PRAAx] ap2 (sumF previousBody) N (pairT c M) ≐ count N M := by
  refine sum_congr_bounded previousBody (sgB bitBody) (pairT c M) M N (.allI (.impI ?_))
  rw [inst2_sgB,bit_body_at]
  simpa only [Syn.shift,subst_pairT] using previous_body_at (Syn.shift M) (Syn.shift c) (var 0)

theorem prefix_count_after (N M c t : PTm n) (ht : Γ ⊢[PRAAx] le t N) (hi : Γ ⊢[PRAAx] lt c t)
    (hc : Γ ⊢[PRAAx] bit M c ≐ zero) : Γ ⊢[PRAAx] count t (insert N M c) ≐ succ (count t M) := by
  have combine : Γ ⊢[PRAAx] count t (insert N M c) ≐ ap2 (sumF (addBody previousBody deltaBody)) t (pairT c M) := by
    refine sum_congr_bounded (sgB bitBody) (addBody previousBody deltaBody) (insert N M c) (pairT c M) t (.allI (.impI ?_))
    let N' := Syn.shift N
    let M' := Syn.shift M
    let c' := Syn.shift c
    let t' := Syn.shift t
    let Δ := lt (var 0) t' :: Γ.map Fm.shift
    have limit : Δ ⊢[PRAAx] le t' N' := by
      simpa only [Δ,t',N',Fm.shift,subst_le,Syn.shift] using ht.shift.wk
    have zeroBit : Δ ⊢[PRAAx] bit M' c' ≐ zero := by
      simpa only [Δ,M',c',Fm.shift,Fm.subst_eq,RationalSubtupleSpan.subst_bit,ConciseIPRA.PTm.subst_zero,Syn.shift] using hc.shift.wk
    have e := indicator_changes N' M' c' (var 0) (lt_of_lt_of_le Prf.hyp0 limit) zeroBit
    rw [inst2_sgB,bit_body_at,inst2_addBody]
    simpa only [Δ,N',M',c',t',Syn.shift,subst_pairT,subst_insert] using
      e.eqTrans (congrAdd (previous_body_at M' c' (var 0)).eqSymm (delta_body_at M' c' (var 0)).eqSymm)
  have oneSum : Γ ⊢[PRAAx] ap2 (sumF deltaBody) t (pairT c M) ≐ one := by
    simpa [deltaBody,inst2,one] using sum_delta (one : PTm 2) (x := M) hi
  exact combine.eqTrans ((sum_add _ _ _ _).eqTrans
    ((congrAdd (previous_sum t M c) oneSum).eqTrans (succ_eq_add_one _).eqSymm))

theorem insert_count (N M c : PTm n) (hi : Γ ⊢[PRAAx] lt c N) (hc : Γ ⊢[PRAAx] bit M c ≐ zero) :
    Γ ⊢[PRAAx] count N (insert N M c) ≐ succ (count N M) :=
  prefix_count_after N M c N (le_refl N) hi hc

theorem prefix_count_before (N M c t : PTm n) (ht : Γ ⊢[PRAAx] le t N) (hc : Γ ⊢[PRAAx] le t c) :
    Γ ⊢[PRAAx] count t (insert N M c) ≐ count t M := by
  refine sum_congr_bounded (sgB bitBody) (sgB bitBody) (insert N M c) M t (.allI (.impI ?_))
  let t' := Syn.shift t
  let N' := Syn.shift N
  let M' := Syn.shift M
  let c' := Syn.shift c
  let Δ := lt (var 0) t' :: Γ.map Fm.shift
  have hq : Δ ⊢[PRAAx] lt (var 0) t' := Prf.hyp0
  have hN : Δ ⊢[PRAAx] le t' N' := by
    simpa only [Δ,t',N',Fm.shift,subst_le,Syn.shift] using ht.shift.wk
  have hc' : Δ ⊢[PRAAx] le t' c' := by
    simpa only [Δ,t',c',Fm.shift,subst_le,Syn.shift] using hc.shift.wk
  have before := lt_of_lt_of_le hq hc'
  have different : Δ ⊢[PRAAx] neg (var 0 ≐ c') :=
    .impI (lt_irrefl c' _ (lt_congr Prf.hyp0 (.eqRefl _) before.wk))
  rw [inst2_sgB,inst2_sgB,bit_body_at,bit_body_at]
  simpa only [Δ,t',N',M',c',Syn.shift,subst_insert] using
    sg_congr (old_bit N' M' c' (var 0) (lt_of_lt_of_le hq hN) different)

theorem inserted_listed (N M c : PTm n) (hi : Γ ⊢[PRAAx] lt c N) : Γ ⊢[PRAAx]
    lt (count c M) (count N (insert N M c)) ⋏ index N (insert N M c) (count c M) ≐ c := by
  have h := selected_listed _ _ _ hi (.impI (succ_ne_zero ((new_bit N M c hi).wk.eqSymm.eqTrans Prf.hyp0)))
  have e := prefix_count_before N M c c (le_of_lt hi) (le_refl c)
  exact .andI (lt_congr e (.eqRefl _) h.andE₁)
    ((Foundations.SequenceComposition.entry_congr (.eqRefl (indices N (insert N M c))) e.eqSymm).eqTrans h.andE₂)

theorem index_rank (N M r : PTm n) (h : Γ ⊢[PRAAx] lt r (count N M)) :
    Γ ⊢[PRAAx] count (index N M r) M ≐ r := by
  have e := Foundations.FilteredEnumerationCode.list_lookup bitBody N M r h
  exact (congrAp2 (sumF (sgB bitBody)) e (.eqRefl M)).eqTrans
    (Foundations.FilteredEnumeration.sel_spec bitBody h).andE₂.andE₂

theorem retained_index (N M c r : PTm n) (h : Γ ⊢[PRAAx] lt r (count N M))
    (hc : Γ ⊢[PRAAx] neg (index N M r ≐ c)) : Γ ⊢[PRAAx]
    lt (count (index N M r) (insert N M c)) (count N (insert N M c)) ⋏
      index N (insert N M c) (count (index N M r) (insert N M c)) ≐ index N M r := by
  have hi := index_bound N M r h
  have same := old_bit N M c (index N M r) hi hc
  exact selected_listed _ _ _ hi (.impI (.impE (index_selected N M r h).wk (same.wk.eqSymm.eqTrans Prf.hyp0)))

theorem retained_before (N M c r : PTm n) (h : Γ ⊢[PRAAx] lt r (count N M))
    (hc : Γ ⊢[PRAAx] lt (index N M r) c) : Γ ⊢[PRAAx]
    lt r (count N (insert N M c)) ⋏ index N (insert N M c) r ≐ index N M r := by
  have whereListed := retained_index N M c r h (.impI (lt_irrefl c _ (lt_congr Prf.hyp0 (.eqRefl _) hc.wk)))
  have sameRank := (prefix_count_before N M c _ (le_of_lt (index_bound N M r h)) (le_of_lt hc)).eqTrans
    (index_rank N M r h)
  exact .andI (lt_congr sameRank (.eqRefl _) whereListed.andE₁)
    ((Foundations.SequenceComposition.entry_congr (.eqRefl (indices N (insert N M c))) sameRank.eqSymm).eqTrans whereListed.andE₂)

theorem retained_after (N M c r : PTm n) (h : Γ ⊢[PRAAx] lt r (count N M)) (hb : Γ ⊢[PRAAx] bit M c ≐ zero)
    (hc : Γ ⊢[PRAAx] lt c (index N M r)) : Γ ⊢[PRAAx]
    lt (succ r) (count N (insert N M c)) ⋏ index N (insert N M c) (succ r) ≐ index N M r := by
  have whereListed := retained_index N M c r h (.impI (lt_irrefl c _ (lt_congr (.eqRefl _) Prf.hyp0 hc.wk)))
  have newRank := (prefix_count_after N M c _ (le_of_lt (index_bound N M r h)) hc hb).eqTrans
    (congrSucc (index_rank N M r h))
  exact .andI (lt_congr newRank (.eqRefl _) whereListed.andE₁)
    ((Foundations.SequenceComposition.entry_congr (.eqRefl (indices N (insert N M c))) newRank.eqSymm).eqTrans whereListed.andE₂)

theorem actual_inserted_mask_range_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (insert (var 0) (var 1) (var 2)) (pw two (var 0))) := closeUniv 3 (insert_bound _ _ _)

theorem actual_inserted_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 0) ⟶ bit (insert (var 0) (var 1) (var 2)) (var 2) ≐ one) :=
  closeUniv 3 (.impI (new_bit (var 0) (var 1) (var 2) Prf.hyp0))

theorem actual_retained_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 0) ⟶ neg (var 3 ≐ var 2) ⟶ bit (insert (var 0) (var 1) (var 2)) (var 3) ≐ bit (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (old_bit (var 0) (var 1) (var 2) (var 3) Prf.hyp1 Prf.hyp0)))

theorem actual_inserted_mask_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 0) ⟶ bit (var 1) (var 2) ≐ zero ⟶ count (var 0) (insert (var 0) (var 1) (var 2)) ≐ succ (count (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (insert_count (var 0) (var 1) (var 2) Prf.hyp1 Prf.hyp0)))

theorem actual_inserted_position_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 0) ⟶ lt (count (var 2) (var 1)) (count (var 0) (insert (var 0) (var 1) (var 2))) ⋏
      index (var 0) (insert (var 0) (var 1) (var 2)) (count (var 2) (var 1)) ≐ var 2) :=
  closeUniv 3 (.impI (inserted_listed _ _ _ Prf.hyp0))

theorem actual_retained_position_before_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (count (var 0) (var 1)) ⟶ lt (index (var 0) (var 1) (var 3)) (var 2) ⟶
      lt (var 3) (count (var 0) (insert (var 0) (var 1) (var 2))) ⋏
      index (var 0) (insert (var 0) (var 1) (var 2)) (var 3) ≐ index (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (retained_before _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_retained_position_after_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (count (var 0) (var 1)) ⟶ bit (var 1) (var 2) ≐ zero ⟶ lt (var 2) (index (var 0) (var 1) (var 3)) ⟶
      lt (succ (var 3)) (count (var 0) (insert (var 0) (var 1) (var 2))) ⋏
      index (var 0) (insert (var 0) (var 1) (var 2)) (succ (var 3)) ≐ index (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (retained_after _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalMinorMaskExtension
