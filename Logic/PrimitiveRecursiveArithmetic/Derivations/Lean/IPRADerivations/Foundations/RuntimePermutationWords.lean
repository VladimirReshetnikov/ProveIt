import IPRADerivations.Foundations.MixedRadixExpansion
import IPRADerivations.Foundations.FilteredEnumerationCode
import IPRADerivations.Foundations.BoundedSyntaxInduction
import IPRADerivations.Core.Parity
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.SubstCommand

/-!
# Numeric permutation words for the runtime determinant

All dimensions, tuples, word codes and digit indices are numerical.
The actual scan has m^m words and retains the in-range, no-repeat tuples.
The mixed-radix proofs give coverage and uniqueness, not equality of
arbitrary outer list codes. Position zero is the least-significant digit,
matching the source word enumeration. This file uses Foundations/Core only.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RuntimePermutationWords

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (m w : PTm n) : PTm n := pairT w m
def radixBody : PTm 2 := sndT (var 1)
def vectorBody : PTm 2 := entry (fstT (var 1)) (var 0)
def horizon (m : PTm n) : PTm n := pw m m
def digit (m w i : PTm n) : PTm n := rem (quo w (pw m i)) m
def digitBody : PTm 2 := digit (sndT (var 1)) (fstT (var 1)) (var 0)
def word (m w : PTm n) : PTm n := sequence digitBody m (data m w)
def encode (P m : PTm n) : PTm n := MixedRadix.Cd radixBody vectorBody m (data m P)
def entriesEqual (P Q m : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ entry (Syn.shift P) (var 0) ≐ entry (Syn.shift Q) (var 0))
def range (P m : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ lt (entry (Syn.shift P) (var 0)) (Syn.shift m))
def distinctFrom (P i : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift i) ⟶ neg (entry (Syn.shift P) (Syn.shift i) ≐ entry (Syn.shift P) (var 0)))
def distinct (P m : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ distinctFrom (Syn.shift P) (var 0))
def tuple (P m : PTm n) : Fm PTm n := length P ≐ m ⋏ (range P m ⋏ distinct P m)

ipra_subst data
ipra_subst horizon
ipra_subst digit
ipra_subst word
ipra_subst encode
ipra_subst entriesEqual [Syn.subst_shift, Syn.shift_subst]
ipra_subst range [Syn.subst_shift, Syn.shift_subst]
ipra_subst distinctFrom [Syn.subst_shift, Syn.shift_subst]
ipra_subst distinct [Syn.subst_shift, Syn.shift_subst]
ipra_subst tuple

theorem radix_at (m w i : PTm n) : Γ ⊢[PRAAx] inst2 radixBody i (data m w) ≐ m := by
  simpa [radixBody,inst2,data] using snd_pair (Γ := Γ) w m
theorem vector_at (P m i : PTm n) : Γ ⊢[PRAAx] inst2 vectorBody i (data m P) ≐ entry P i := by
  simpa [vectorBody,inst2,data] using entry_congr (Γ := Γ) (fst_pair P m) (.eqRefl i)
theorem places (m w k : PTm n) : Γ ⊢[PRAAx] MixedRadix.Pl radixBody k (data m w) ≐ pw m k := by
  apply prod_const_of
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_data] using radix_at (Syn.shift m) (Syn.shift w) (var 0)
theorem radices_positive (m w : PTm n) : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift m) ⟶ lt zero (inst2 radixBody (var 0) (Syn.shift (data m w)))) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_data] using
    lt_congr (.eqRefl _) (radix_at (Syn.shift m) (Syn.shift w) (var 0)).eqSymm
      (lt_of_le_of_lt (zero_le _) Prf.hyp0)
theorem decoded_digit (m w i : PTm n) : Γ ⊢[PRAAx]
    inst2 (MixedRadixExpansion.dgB radixBody) i (data m w) ≐ digit m w i := by
  rw [MixedRadixExpansion.inst2_dgB]
  exact congrAp2 remF (congrAp2 quoF (fst_pair w m) (places m w i)) (radix_at m w i)
theorem digit_bound (m w i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx] lt (digit m w i) m := by
  have all := MixedRadixExpansion.digits_bounded (radices_positive (Γ := Γ) m w)
  have gate : Γ ⊢[PRAAx] lt i m ⟶
      lt (inst2 (MixedRadixExpansion.dgB radixBody) i (data m w)) (inst2 radixBody i (data m w)) := by
    simpa only [Fm.subst_imp,subst_lt,subst_inst2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact lt_congr (decoded_digit m w i) (radix_at m w i) (.impE gate hi)

theorem digit_body_at (m w i : PTm n) : Γ ⊢[PRAAx]
    inst2 digitBody i (data m w) ≐ digit m w i := by
  simp only [digitBody,inst2,subst_digit,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrAp2 remF (congrAp2 quoF (fst_pair _ _) (congrAp2 powF (.eqRefl _) (snd_pair _ _))) (snd_pair _ _)
theorem word_length (m w : PTm n) : Γ ⊢[PRAAx] length (word m w) ≐ m := sequence_length _ _ _
theorem word_lookup (m w i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    entry (word m w) i ≐ digit m w i :=
  (sequence_decode digitBody hi).eqTrans (digit_body_at _ _ _)

theorem range_at (P m i : PTm n) (h : Γ ⊢[PRAAx] range P m) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    lt (entry P i) m := by
  have gate : Γ ⊢[PRAAx] lt i m ⟶ lt (entry P i) m := by
    simpa only [range,Fm.subst_imp,subst_lt,subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE gate hi
theorem entries_at (P Q m i : PTm n) (h : Γ ⊢[PRAAx] entriesEqual P Q m) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    entry P i ≐ entry Q i := by
  have gate : Γ ⊢[PRAAx] lt i m ⟶ entry P i ≐ entry Q i := by
    simpa only [entriesEqual,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE gate hi
theorem distinct_at (P m i j : PTm n) (h : Γ ⊢[PRAAx] distinct P m)
    (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt j i) : Γ ⊢[PRAAx] neg (entry P i ≐ entry P j) := by
  have outer : Γ ⊢[PRAAx] lt i m ⟶ distinctFrom P i := by
    simpa only [distinct,Fm.subst_imp,subst_lt,subst_distinctFrom,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  have gate : Γ ⊢[PRAAx] lt j i ⟶ neg (entry P i ≐ entry P j) := by
    simpa [distinctFrom,neg] using (Prf.impE outer hi).allE j
  exact .impE gate hj

theorem encode_bound (P m : PTm n) (h : Γ ⊢[PRAAx] range P m) : Γ ⊢[PRAAx] lt (encode P m) (horizon m) := by
  have all : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift m) ⟶
      lt (inst2 vectorBody (var 0) (Syn.shift (data m P))) (inst2 radixBody (var 0) (Syn.shift (data m P)))) := by
    refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] range (Syn.shift P) (Syn.shift m) := by
      simpa only [Fm.shift,subst_range,Syn.shift] using h.shift
    simpa only [Syn.shift,subst_data] using lt_congr (vector_at _ _ _).eqSymm (radix_at _ _ _).eqSymm
      (range_at _ _ _ hs.wk Prf.hyp0)
  exact lt_congr (.eqRefl _) (places m P m) (MixedRadix.code_lt _ _ _ _ all)

theorem suffix_balance (m i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    succ i+monus m (succ i) ≐ m := (eq_add_of_le hi).eqSymm
theorem encode_decode (P m i : PTm n) (h : Γ ⊢[PRAAx] range P m) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    digit m (encode P m) i ≐ entry P i := by
  let t := monus m (succ i)
  have span := suffix_balance m i hi
  have all : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ i+t)) ⟶
      lt (inst2 vectorBody (var 0) (Syn.shift (data m P))) (inst2 radixBody (var 0) (Syn.shift (data m P)))) := by
    refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] range (Syn.shift P) (Syn.shift m) := by
      simpa only [Fm.shift,subst_range,Syn.shift] using h.shift
    have ss : Γ.map Fm.shift ⊢[PRAAx] Syn.shift (succ i+t) ≐ Syn.shift m := by
      simpa only [Fm.shift,Fm.subst_eq,Syn.shift,t] using span.shift
    simpa only [Syn.shift,subst_data] using lt_congr (vector_at _ _ _).eqSymm (radix_at _ _ _).eqSymm
      (range_at _ _ _ hs.wk (lt_congr (.eqRefl _) ss.wk Prf.hyp0))
  have codeEq : Γ ⊢[PRAAx] MixedRadix.Cd radixBody vectorBody (succ i+t) (data m P) ≐ encode P m :=
    congrAp2 (sumF (MixedRadix.dP radixBody vectorBody)) span (.eqRefl _)
  have e := MixedRadix.decode all
  exact (congrAp2 remF (congrAp2 quoF codeEq (places m P i)) (radix_at m P i)).eqSymm.eqTrans
    (e.eqTrans (vector_at _ _ _))

theorem encode_entries (P Q m : PTm n) (h : Γ ⊢[PRAAx] entriesEqual P Q m) : Γ ⊢[PRAAx]
    encode P m ≐ encode Q m := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] entriesEqual (Syn.shift P) (Syn.shift Q) (Syn.shift m) := by
    simpa only [Fm.shift,subst_entriesEqual,Syn.shift] using h.shift
  simp only [Syn.shift,subst_data,MixedRadix.inst2_dP]
  exact congrMul
    ((vector_at _ _ _).eqTrans ((entries_at _ _ _ _ hs.wk Prf.hyp0).eqTrans (vector_at _ _ _).eqSymm))
    ((places _ _ _).eqTrans (places _ _ _).eqSymm)

theorem encode_word (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon m)) : Γ ⊢[PRAAx]
    encode (word m w) m ≐ w := by
  have words : Γ ⊢[PRAAx] encode (word m w) m ≐
      MixedRadix.Cd radixBody (MixedRadixExpansion.dgB radixBody) m (data m w) := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    simp only [Syn.shift,subst_data,subst_word,MixedRadix.inst2_dP]
    exact congrMul
      ((vector_at _ _ _).eqTrans ((word_lookup _ _ _ Prf.hyp0).eqTrans (decoded_digit _ _ _).eqSymm))
      ((places _ _ _).eqTrans (places _ _ _).eqSymm)
  have rangeWord : Γ ⊢[PRAAx] lt (fstT (data m w)) (MixedRadix.Pl radixBody m (data m w)) :=
    lt_congr (fst_pair w m).eqSymm (places m w m).eqSymm hw
  exact words.eqTrans ((MixedRadixExpansion.reencode (radices_positive m w) rangeWord).eqTrans (fst_pair _ _))

theorem word_unique (m w v : PTm n) (hw : Γ ⊢[PRAAx] lt w (horizon m))
    (hv : Γ ⊢[PRAAx] lt v (horizon m)) (h : Γ ⊢[PRAAx] entriesEqual (word m w) (word m v) m) : Γ ⊢[PRAAx] w ≐ v :=
  (encode_word m w hw).eqSymm.eqTrans ((encode_entries _ _ _ h).eqTrans (encode_word m v hv))


theorem tuple_transfer (P Q m : PTm n) (hP : Γ ⊢[PRAAx] tuple P m)
    (hQ : Γ ⊢[PRAAx] length Q ≐ m) (h : Γ ⊢[PRAAx] entriesEqual P Q m) : Γ ⊢[PRAAx] tuple Q m := by
  refine .andI hQ (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    have ps : Γ.map Fm.shift ⊢[PRAAx] tuple (Syn.shift P) (Syn.shift m) := by
      simpa only [Fm.shift,subst_tuple,Syn.shift] using hP.shift
    have es : Γ.map Fm.shift ⊢[PRAAx] entriesEqual (Syn.shift P) (Syn.shift Q) (Syn.shift m) := by
      simpa only [Fm.shift,subst_entriesEqual,Syn.shift] using h.shift
    exact lt_congr (entries_at _ _ _ _ es.wk Prf.hyp0) (.eqRefl _)
      (range_at _ _ _ (.andE₁ (.andE₂ ps.wk)) Prf.hyp0)
  · refine .allI (.impI (.allI (.impI ?_)))
    let Δ := lt (var 0) (var 1) :: (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift).map Fm.shift
    have ps : Δ ⊢[PRAAx] tuple (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift m)) := by
      simpa only [Δ,Fm.shift,subst_tuple,Syn.shift,List.map_cons] using hP.shift.wk.shift.wk
    have es : Δ ⊢[PRAAx] entriesEqual (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift Q)) (Syn.shift (Syn.shift m)) := by
      simpa only [Δ,Fm.shift,subst_entriesEqual,Syn.shift,List.map_cons] using h.shift.wk.shift.wk
    have hi : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
      simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.subst_var,Syn.shift,Fin.succ_zero_eq_one] using
        (Prf.hyp1 : Δ ⊢[PRAAx] Fm.shift (lt (var 0) (Syn.shift m)))
    have hj : Δ ⊢[PRAAx] lt (var 0) (var 1) := Prf.hyp0
    have ei := entries_at _ _ _ (var 1) es hi
    have ej := entries_at _ _ _ (var 0) es (lt_of_lt_of_le hj (le_of_lt hi))
    have no := distinct_at _ _ (var 1) (var 0) (.andE₂ (.andE₂ ps)) hi hj
    exact .impI (.impE no.wk (ei.wk.eqTrans (Prf.hyp0.eqTrans ej.wk.eqSymm)))

theorem encoded_entries (P m : PTm n) (h : Γ ⊢[PRAAx] range P m) : Γ ⊢[PRAAx]
    entriesEqual P (word m (encode P m)) m := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] range (Syn.shift P) (Syn.shift m) := by
    simpa only [Fm.shift,subst_range,Syn.shift] using h.shift
  simpa only [Syn.shift,subst_word,subst_encode] using
    ((word_lookup (Syn.shift m) (encode (Syn.shift P) (Syn.shift m)) (var 0) Prf.hyp0).eqTrans
      (encode_decode _ _ _ hs.wk Prf.hyp0)).eqSymm

theorem encoded_tuple (P m : PTm n) (h : Γ ⊢[PRAAx] tuple P m) : Γ ⊢[PRAAx]
    tuple (word m (encode P m)) m :=
  tuple_transfer _ _ _ h (word_length _ _) (encoded_entries _ _ (.andE₁ (.andE₂ h)))

/-- The bounded test includes actual tuple length, range and pairwise distinctness. -/
def tupleSyntax (P m : PTm n) : BFm n := .and (.eq (length P) m)
  (.and (.all m (.lt (entry (Syn.shift P) (var 0)) (Syn.shift m)))
    (.all m (.all (var 0) (.not (.eq (entry (Syn.shift (Syn.shift P)) (var 1))
      (entry (Syn.shift (Syn.shift P)) (var 0)))))))
def permutation (m w : PTm n) : Fm PTm n := tuple (word m w) m
def permutationSyntax (m w : PTm n) : BFm n := tupleSyntax (word m w) m
def checkerF : PR 2 := LeanProofs.IPRA.Foundations.BoundedSyntax.bitF (permutationSyntax (var 0) (var 1))
def permutationBit (m w : PTm n) : PTm n := ap2 checkerF m w
ipra_subst permutation
ipra_subst permutationBit
theorem tuple_syntax_formula (P m : PTm n) : formula (tupleSyntax P m) = tuple P m := by
  simp [tupleSyntax,formula,BFm.lt,BFm.le,tuple,range,distinct,distinctFrom,lt,le,neg,Syn.shift]
theorem checker_at (m w : PTm n) : Γ ⊢[PRAAx] permutationBit m w ≐
    LeanProofs.IPRA.Foundations.BoundedSyntax.bit (permutationSyntax (var 0) (var 1)) ![m,w] := by
  simpa only [permutationBit,checkerF,ap2] using
    LeanProofs.IPRA.Foundations.BoundedSyntax.program_correct (permutationSyntax (var 0) (var 1)) ![m,w]
theorem checker_reflection (m w : PTm n) : Γ ⊢[PRAAx] Fm.iff (permutationBit m w ≐ one) (permutation m w) := by
  have r : Γ ⊢[PRAAx] Fm.iff
      (LeanProofs.IPRA.Foundations.BoundedSyntax.bit (permutationSyntax (var 0) (var 1)) ![m,w] ≐ one)
      (permutation m w) := by
    simpa only [permutationSyntax,tuple_syntax_formula,subst_tuple,subst_word,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,permutation] using
      LeanProofs.IPRA.Foundations.BoundedSyntax.bounded_reflection (permutationSyntax (var 0) (var 1)) ![m,w]
  exact .iffI (.impI (.iffMp r.wk ((checker_at _ _).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((checker_at _ _).eqTrans (.iffMpr r.wk Prf.hyp0)))
theorem checker_cases (m w : PTm n) : Γ ⊢[PRAAx]
    (permutationBit m w ≐ zero) ⋎ (permutationBit m w ≐ one) :=
  .orE (LeanProofs.IPRA.Foundations.BoundedSyntax.bit_cases (permutationSyntax (var 0) (var 1)) ![m,w])
    (.orI₁ ((checker_at _ _).eqTrans Prf.hyp0)) (.orI₂ ((checker_at _ _).eqTrans Prf.hyp0))


/-- Increasing stored word codes, filtered by the proved bounded test. -/
def keepBody : PTm 2 := permutationBit (var 1) (var 0)
def count (m : PTm n) : PTm n := FilteredEnumerationCode.count keepBody (horizon m) m
def words (m : PTm n) : PTm n := FilteredEnumerationCode.list keepBody (horizon m) m
def position (P m : PTm n) : PTm n := FilteredEnumeration.rank keepBody (encode P m) m
def codeBound (m : PTm n) : PTm n := FilteredEnumerationCode.codeBound keepBody (horizon m) m
ipra_subst count
ipra_subst words
ipra_subst position [FilteredEnumeration.rank]
ipra_subst codeBound
theorem keep_at (m w : PTm n) : inst2 keepBody w m = permutationBit m w := by simp [keepBody,inst2]
theorem words_length (m : PTm n) : Γ ⊢[PRAAx] length (words m) ≐ count m :=
  FilteredEnumerationCode.list_length _ _ _
theorem count_bound (m : PTm n) : Γ ⊢[PRAAx] le (count m) (horizon m) :=
  FilteredEnumerationCode.count_le _ _ _
theorem words_code_bound (m : PTm n) : Γ ⊢[PRAAx] lt (words m) (codeBound m) :=
  FilteredEnumerationCode.size_bound _ _ _
theorem retained_bound (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m)) : Γ ⊢[PRAAx]
    lt (entry (words m) r) (horizon m) := FilteredEnumerationCode.entry_bound _ _ _ _ hr
theorem retained_valid (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m)) : Γ ⊢[PRAAx]
    permutation m (entry (words m) r) := by
  have nonzero : Γ ⊢[PRAAx] neg (permutationBit m (entry (words m) r) ≐ zero) := by
    simpa only [keep_at,words] using FilteredEnumerationCode.entry_valid keepBody (horizon m) m r hr
  refine .orE (checker_cases m (entry (words m) r)) (.botE _ (.impE nonzero.wk Prf.hyp0)) ?_
  exact (checker_reflection _ _).iffMp Prf.hyp0
theorem retained_increasing (m r s : PTm n) (hrs : Γ ⊢[PRAAx] lt r s)
    (hs : Γ ⊢[PRAAx] lt s (count m)) : Γ ⊢[PRAAx]
    lt (entry (words m) r) (entry (words m) s) := FilteredEnumerationCode.increasing _ _ _ _ _ hrs hs
theorem listed (P m : PTm n) (h : Γ ⊢[PRAAx] tuple P m) : Γ ⊢[PRAAx]
    lt (position P m) (count m) ⋏ (entry (words m) (position P m) ≐ encode P m) := by
  apply FilteredEnumerationCode.listed
  · exact encode_bound _ _ (.andE₁ (.andE₂ h))
  · rw [keep_at]
    have one := (checker_reflection m (encode P m)).iffMpr (encoded_tuple _ _ h)
    exact .impI (BoundedReflection.one_ne_zero _ (one.wk.eqSymm.eqTrans Prf.hyp0))
theorem retained_position_unique (m r s : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m))
    (hs : Γ ⊢[PRAAx] lt s (count m)) (he : Γ ⊢[PRAAx] entry (words m) r ≐ entry (words m) s) :
    Γ ⊢[PRAAx] r ≐ s := by
  apply le_antisymm
  · refine .orE (lt_or_le s r) ?_ Prf.hyp0
    exact .botE _ (lt_irrefl _ Fm.bot (lt_congr (.eqRefl _) he.wk (retained_increasing _ _ _ Prf.hyp0 hr.wk)))
  · refine .orE (lt_or_le r s) ?_ Prf.hyp0
    exact .botE _ (lt_irrefl _ Fm.bot (lt_congr he.wk (.eqRefl _) (retained_increasing _ _ _ Prf.hyp0 hs.wk)))


def identity (m : PTm n) : PTm n := sequence (var 0 : PTm 2) m zero
ipra_subst identity
theorem identity_length (m : PTm n) : Γ ⊢[PRAAx] length (identity m) ≐ m := sequence_length _ _ _
theorem identity_lookup (m i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    entry (identity m) i ≐ i := by
  simpa only [identity,inst2,Syn.subst_var,Matrix.cons_val_zero] using
    (sequence_decode (var 0 : PTm 2) (x := zero) hi)
theorem identity_tuple (m : PTm n) : Γ ⊢[PRAAx] tuple (identity m) m := by
  refine .andI (identity_length _) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_identity] using
      lt_congr (identity_lookup (Syn.shift m) (var 0) Prf.hyp0).eqSymm (.eqRefl _) Prf.hyp0
  · refine .allI (.impI (.allI (.impI ?_)))
    let Δ := lt (var 0) (var 1) :: (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift).map Fm.shift
    have hi : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
      simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.subst_var,Syn.shift,Fin.succ_zero_eq_one] using
        (Prf.hyp1 : Δ ⊢[PRAAx] Fm.shift (lt (var 0) (Syn.shift m)))
    have hj : Δ ⊢[PRAAx] lt (var 0) (var 1) := Prf.hyp0
    have ei := identity_lookup _ (var 1) hi
    have ej := identity_lookup _ (var 0) (lt_of_lt_of_le hj (le_of_lt hi))
    have no : Δ ⊢[PRAAx] neg (entry (identity (Syn.shift (Syn.shift m))) (var 1) ≐
        entry (identity (Syn.shift (Syn.shift m))) (var 0)) := by
      refine .impI ?_
      exact lt_irrefl _ Fm.bot (lt_congr (.eqRefl _) (ei.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans ej.wk)) hj.wk)
    simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,subst_identity] using no

theorem words_nonempty (m : PTm n) : Γ ⊢[PRAAx] le one (count m) :=
  lt_of_le_of_lt (zero_le _) (.andE₁ (listed (identity m) m (identity_tuple m)))
theorem count_zero : Γ ⊢[PRAAx] count (zero : PTm n) ≐ one :=
  le_antisymm (le_congr (.eqRefl _) (pw_zero zero) (count_bound zero)) (words_nonempty zero)
theorem count_one : Γ ⊢[PRAAx] count (one : PTm n) ≐ one :=
  le_antisymm (le_congr (.eqRefl _) (pw_one one) (count_bound one)) (words_nonempty one)

/-- Actual inversion indicators: positions i<j with digit_j<digit_i. -/
def inversionSyntax (m w i j : PTm n) : BFm n :=
  .and (.lt i j) (.lt (digit m w j) (digit m w i))
def inversionF : PR 4 := LeanProofs.IPRA.Foundations.BoundedSyntax.bitF
  (inversionSyntax (var 0) (var 1) (var 2) (var 3))
def inversionBit (m w i j : PTm n) : PTm n := app inversionF ![m,w,i,j]
def inversionColumn : PTm 2 := inversionBit (sndT (sndT (var 1))) (fstT (sndT (var 1)))
  (fstT (var 1)) (var 0)
def rowPrefix (m w i t : PTm n) : PTm n := ap2 (sumF inversionColumn) t (pairT i (data m w))
def inversionRow : PTm 2 := rowPrefix (sndT (var 1)) (fstT (var 1)) (var 0) (sndT (var 1))
def inversionPrefix (m w t : PTm n) : PTm n := ap2 (sumF inversionRow) t (data m w)
def inversions (m w : PTm n) : PTm n := inversionPrefix m w m
def parity (m w : PTm n) : PTm n := par (inversions m w)
@[simp] theorem subst_inversionBit {l : ℕ} (σ : Fin n → PTm l) (m w i j : PTm n) :
    Syn.subst σ (inversionBit m w i j) = inversionBit (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ i) (Syn.subst σ j) := by
  simp only [inversionBit,ConciseIPRA.PTm.subst_app]
  congr 1
  funext k
  fin_cases k <;> rfl
@[simp] theorem subst_rowPrefix {l : ℕ} (σ : Fin n → PTm l) (m w i t : PTm n) :
    Syn.subst σ (rowPrefix m w i t) = rowPrefix (Syn.subst σ m) (Syn.subst σ w) (Syn.subst σ i) (Syn.subst σ t) := by simp [rowPrefix]
ipra_subst inversionPrefix
ipra_subst inversions
ipra_subst parity
theorem inversion_at (m w i j : PTm n) : Γ ⊢[PRAAx] inversionBit m w i j ≐
    LeanProofs.IPRA.Foundations.BoundedSyntax.bit (inversionSyntax (var 0) (var 1) (var 2) (var 3)) ![m,w,i,j] := by
  simpa only [inversionBit,inversionF] using
    LeanProofs.IPRA.Foundations.BoundedSyntax.program_correct (inversionSyntax (var 0) (var 1) (var 2) (var 3)) ![m,w,i,j]
theorem inversion_reflection (m w i j : PTm n) : Γ ⊢[PRAAx] Fm.iff
    (inversionBit m w i j ≐ one) (lt i j ⋏ lt (digit m w j) (digit m w i)) := by
  have r : Γ ⊢[PRAAx] Fm.iff
      (LeanProofs.IPRA.Foundations.BoundedSyntax.bit (inversionSyntax (var 0) (var 1) (var 2) (var 3)) ![m,w,i,j] ≐ one)
      (lt i j ⋏ lt (digit m w j) (digit m w i)) := by
    simpa [inversionSyntax,formula,BFm.lt,BFm.le,lt,le] using
      LeanProofs.IPRA.Foundations.BoundedSyntax.bounded_reflection (inversionSyntax (var 0) (var 1) (var 2) (var 3)) ![m,w,i,j]
  exact .iffI (.impI (.iffMp r.wk ((inversion_at _ _ _ _).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((inversion_at _ _ _ _).eqTrans (.iffMpr r.wk Prf.hyp0)))
theorem inversion_cases (m w i j : PTm n) : Γ ⊢[PRAAx]
    (inversionBit m w i j ≐ zero) ⋎ (inversionBit m w i j ≐ one) :=
  .orE (LeanProofs.IPRA.Foundations.BoundedSyntax.bit_cases (inversionSyntax (var 0) (var 1) (var 2) (var 3)) ![m,w,i,j])
    (.orI₁ ((inversion_at _ _ _ _).eqTrans Prf.hyp0)) (.orI₂ ((inversion_at _ _ _ _).eqTrans Prf.hyp0))
theorem inversion_diagonal (m w i : PTm n) : Γ ⊢[PRAAx] inversionBit m w i i ≐ zero :=
  .orE (inversion_cases m w i i) Prf.hyp0
    (lt_irrefl _ _ (.andE₁ ((inversion_reflection m w i i).iffMp Prf.hyp0)))
theorem inversion_column_at (m w i j : PTm n) : Γ ⊢[PRAAx]
    inst2 inversionColumn j (pairT i (data m w)) ≐ inversionBit m w i j := by
  simp only [inversionColumn,inst2,subst_inversionBit,subst_sndT,subst_fstT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,data]
  simpa using
    Prf.eqCongr (Γ := Γ) (inversionBit (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![sndT (sndT (pairT i (pairT w m))),fstT (sndT (pairT i (pairT w m))),fstT (pairT i (pairT w m)),j])
    (σ' := ![m,w,i,j]) (fun k => by
      fin_cases k
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact fst_pair _ _
      · exact .eqRefl _)
theorem inversion_row_at (m w i : PTm n) : Γ ⊢[PRAAx]
    inst2 inversionRow i (data m w) ≐ rowPrefix m w i m := by
  simp only [inversionRow,inst2,subst_rowPrefix,subst_sndT,subst_fstT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,data]
  ipra_congr (rowPrefix (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [snd_pair _ _, fst_pair _ _, .eqRefl i, snd_pair _ _]
theorem row_zero (m w i : PTm n) : Γ ⊢[PRAAx] rowPrefix m w i zero ≐ zero := sum_zero _ _
theorem row_succ (m w i t : PTm n) : Γ ⊢[PRAAx]
    rowPrefix m w i (succ t) ≐ rowPrefix m w i t+inversionBit m w i t :=
  (sum_succ' _ _ _).eqTrans (congrAdd (.eqRefl _) (inversion_column_at _ _ _ _))
theorem inversion_prefix_zero (m w : PTm n) : Γ ⊢[PRAAx] inversionPrefix m w zero ≐ zero := sum_zero _ _
theorem inversion_prefix_succ (m w t : PTm n) : Γ ⊢[PRAAx]
    inversionPrefix m w (succ t) ≐ inversionPrefix m w t+rowPrefix m w t m :=
  (sum_succ' _ _ _).eqTrans (congrAdd (.eqRefl _) (inversion_row_at _ _ _))
theorem inversions_zero (w : PTm n) : Γ ⊢[PRAAx] inversions zero w ≐ zero := inversion_prefix_zero _ _
theorem inversions_one (w : PTm n) : Γ ⊢[PRAAx] inversions one w ≐ zero :=
  (inversion_prefix_succ _ _ zero).eqTrans
    ((congrAdd (inversion_prefix_zero _ _) ((row_succ _ _ _ zero).eqTrans
      ((congrAdd (row_zero _ _ _) (inversion_diagonal _ _ _)).eqTrans (add_zero _)))).eqTrans (add_zero _))
theorem parity_cases (m w : PTm n) : Γ ⊢[PRAAx] (parity m w ≐ zero) ⋎ (parity m w ≐ one) := par_cases _
theorem parity_zero (w : PTm n) : Γ ⊢[PRAAx] parity zero w ≐ zero := (congrAp1 parF (inversions_zero _)).eqTrans par_zero
theorem parity_one (w : PTm n) : Γ ⊢[PRAAx] parity one w ≐ zero := (congrAp1 parF (inversions_one _)).eqTrans par_zero


/-! The generated output retains the actual scan and its genuine word metadata.
The displayed parity is an unsigned bit; Gaussian sign selection belongs to
its Analysis consumer, where even is +1 and odd is -1. -/
def output (m w : PTm n) : PTm n := pairT (words m) (pairT (count m) (pairT (word m w)
  (pairT (permutationBit m w) (pairT (inversions m w) (parity m w)))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (m w : PTm n) : PTm n := ap2 outputF m w
def boundF : PR 1 := PTm.toPR (codeBound (var 0))
ipra_subst output
ipra_subst run
theorem program_at (m w : PTm n) : Γ ⊢[PRAAx] run m w ≐ output m w := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1)) ![m,w]
theorem bound_program_at (m : PTm n) : Γ ⊢[PRAAx] ap1 boundF m ≐ codeBound m := by
  simpa [boundF,ap1] using toPR_eq (Γ := Γ) (codeBound (var 0)) ![m]
theorem returned_words (m w : PTm n) : Γ ⊢[PRAAx] fstT (run m w) ≐ words m :=
  (congrFst (program_at _ _)).eqTrans (fst_pair _ _)
theorem returned_count (m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run m w)) ≐ count m :=
  (congrFst ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_word (m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run m w))) ≐ word m w :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_bit (m w : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run m w)))) ≐ permutationBit m w :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_inversions (m w : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (sndT (run m w))))) ≐ inversions m w :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_parity (m w : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (sndT (run m w))))) ≐ parity m w :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_words_length (m w : PTm n) : Γ ⊢[PRAAx] length (fstT (run m w)) ≐ count m :=
  (congrFst (returned_words _ _)).eqTrans (words_length _)
theorem returned_size_bound (m w : PTm n) : Γ ⊢[PRAAx] lt (fstT (run m w)) (ap1 boundF m) :=
  lt_congr (returned_words _ _).eqSymm (bound_program_at _).eqSymm (words_code_bound _)

/-! Every numerical dimension, code, tuple and index is quantified in these
ordinary PRA statements. No fixed external Fin(m) permutation is substituted. -/
theorem actual_word_codec_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (range (var 0) (var 1) ⟶ lt (var 2) (var 1) ⟶
      digit (var 1) (encode (var 0) (var 1)) (var 2) ≐ entry (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (encode_decode _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_word_reencode_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (horizon (var 0)) ⟶ encode (word (var 0) (var 1)) (var 0) ≐ var 1) :=
  closeUniv 2 (.impI (encode_word _ _ Prf.hyp0))
theorem actual_tuple_coverage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (tuple (var 0) (var 1) ⟶
      (lt (position (var 0) (var 1)) (count (var 1)) ⋏
        (entry (words (var 1)) (position (var 0) (var 1)) ≐ encode (var 0) (var 1)))) :=
  closeUniv 2 (.impI (listed _ _ Prf.hyp0))
theorem actual_retained_words_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (count (var 0)) ⟶
      (lt (entry (words (var 0)) (var 1)) (horizon (var 0)) ⋏
        tuple (word (var 0) (entry (words (var 0)) (var 1))) (var 0))) :=
  closeUniv 2 (.impI (.andI (retained_bound _ _ Prf.hyp0) (retained_valid _ _ Prf.hyp0)))
theorem actual_word_uniqueness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (horizon (var 0)) ⟶ lt (var 2) (horizon (var 0)) ⟶
      entriesEqual (word (var 0) (var 1)) (word (var 0) (var 2)) (var 0) ⟶ var 1 ≐ var 2) :=
  closeUniv 3 (.impI (.impI (.impI (word_unique _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_retained_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (count (var 0)) ⟶ lt (var 2) (count (var 0)) ⟶
      entry (words (var 0)) (var 1) ≐ entry (words (var 0)) (var 2) ⟶ var 1 ≐ var 2) :=
  closeUniv 3 (.impI (.impI (.impI (retained_position_unique _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_inversion_bit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (inversionBit (var 0) (var 1) (var 2) (var 3) ≐ one)
      (lt (var 2) (var 3) ⋏ lt (digit (var 0) (var 1) (var 3)) (digit (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (inversion_reflection _ _ _ _)
theorem actual_parity_bit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((parity (var 0) (var 1) ≐ zero) ⋎ (parity (var 0) (var 1) ≐ one)) := closeUniv 2 (parity_cases _ _)
theorem empty_and_singleton_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((count zero ≐ one) ⋏ ((count one ≐ one) ⋏ ((parity zero (var 0) ≐ zero) ⋏ (parity one (var 0) ≐ zero)))) :=
  closeUniv 1 (.andI count_zero (.andI count_one (.andI (parity_zero _) (parity_one _))))
theorem actual_word_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_stored_scan_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((length (fstT (run (var 0) (var 1))) ≐ count (var 0)) ⋏
      lt (fstT (run (var 0) (var 1))) (ap1 boundF (var 0))) :=
  closeUniv 2 (.andI (returned_words_length _ _) (returned_size_bound _ _))

end LeanProofs.IPRA.Foundations.RuntimePermutationWords
