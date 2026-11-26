import IPRADerivations.Algebra.QuadraticTowerScalarBudget
import IPRADerivations.Algebra.QuadraticTowerCoefficients
import IPRADerivations.Foundations.MixedRadixExpansion

/-!
# Actual bounded scalar-array codes for numerical quadratic-tower tables

At internal depth h the actual sequence normalizes the first 2^h original
rational entries. Their proved scalar heights give a genuine mixed-radix
code below S(B)^(2^h). Decoding recovers each actual normalized coefficient,
hence its original rational value, without requiring canonical raw inputs
or equating arbitrary outer list codes. This supplies an enumeration horizon
for arithmetic tables; recursive tower multiplication remains separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerArrayCodec

open_ipra
open LeanProofs.IPRA.Analysis
open QuadraticTowerScalarBudget (height codeCap)
open QuadraticTowerCoefficients (width)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations
open RationalArgmin (rationalEq rationalEq_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def arrayHeight (h A B : PTm n) : Fm PTm n := .all
  (lt (var 0) (width (Syn.shift h)) ⟶ height (entry (Syn.shift A) (var 0)) (Syn.shift B))
def boundedEntries (A W S : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift W) ⟶ lt (entry (Syn.shift A) (var 0)) (Syn.shift S))
def normalizeBody : PTm 2 := RationalArithmetic.recode (entry (var 1) (var 0))
def normalized (h A : PTm n) : PTm n := sequence normalizeBody (width h) A
def data (S A : PTm n) : PTm n := pairT S A
def radixBody : PTm 2 := fstT (var 1)
def vectorBody : PTm 2 := entry (sndT (var 1)) (var 0)
def packed (A W S : PTm n) : PTm n := MixedRadix.Cd radixBody vectorBody W (data S A)
def digit (S w i : PTm n) : PTm n := rem (quo w (pw S i)) S
def digitBody : PTm 2 := digit (fstT (var 1)) (sndT (var 1)) (var 0)
def decoded (W S w : PTm n) : PTm n := sequence digitBody W (data S w)
def code (h A B : PTm n) : PTm n := packed (normalized h A) (width h) (codeCap B)
def horizon (h B : PTm n) : PTm n := pw (codeCap B) (width h)
def restored (h A B : PTm n) : PTm n := decoded (width h) (codeCap B) (code h A B)

ipra_subst arrayHeight [Syn.subst_shift, Syn.shift_subst]
ipra_subst boundedEntries [Syn.subst_shift, Syn.shift_subst]
ipra_subst normalized
ipra_subst data
ipra_subst packed
ipra_subst digit
ipra_subst decoded
ipra_subst code
ipra_subst horizon
ipra_subst restored

theorem height_at (h A B i : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A B)
    (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx] height (entry A i) B := by
  have rule : Γ ⊢[PRAAx] lt i (width h) ⟶ height (entry A i) B := by
    simpa [arrayHeight] using ha.allE i
  exact .impE rule hi
theorem bounded_at (A W S i : PTm n) (ha : Γ ⊢[PRAAx] boundedEntries A W S)
    (hi : Γ ⊢[PRAAx] lt i W) : Γ ⊢[PRAAx] lt (entry A i) S := by
  have rule : Γ ⊢[PRAAx] lt i W ⟶ lt (entry A i) S := by simpa [boundedEntries] using ha.allE i
  exact .impE rule hi
theorem normalized_length (h A : PTm n) : Γ ⊢[PRAAx] length (normalized h A) ≐ width h := sequence_length _ _ _
theorem normalize_body_at (A i : PTm n) : inst2 normalizeBody i A = RationalArithmetic.recode (entry A i) := by
  simp [normalizeBody,inst2]
theorem normalized_lookup (h A i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) :
    Γ ⊢[PRAAx] entry (normalized h A) i ≐ RationalArithmetic.recode (entry A i) := by
  simpa only [normalized,normalize_body_at] using sequence_decode (Γ := Γ) normalizeBody (x := A) hi
theorem normalized_canonical (h A i : PTm n) (hi : Γ ⊢[PRAAx] lt i (width h)) :
    Γ ⊢[PRAAx] RationalNormalForm.wellFormed (entry (normalized h A) i) :=
  RationalArithmetic.guard_congr (normalized_lookup h A i hi) (RationalArithmetic.recode_guard _)
theorem normalized_height (h A B i : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A B)
    (hi : Γ ⊢[PRAAx] lt i (width h)) : Γ ⊢[PRAAx] height (entry (normalized h A) i) B :=
  QuadraticTowerScalarBudget.height_congr (normalized_lookup h A i hi).eqSymm (.eqRefl _)
    (QuadraticTowerScalarBudget.recode_height _ _ (height_at h A B i ha hi))
theorem normalized_bounded (h A B : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A B) :
    Γ ⊢[PRAAx] boundedEntries (normalized h A) (width h) (codeCap B) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] arrayHeight (Syn.shift h) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_arrayHeight,Syn.shift] using ha.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have b := QuadraticTowerScalarBudget.canonical_code_bound _ _
    (normalized_canonical (Syn.shift h) (Syn.shift A) (var 0) hi)
    (normalized_height (Syn.shift h) (Syn.shift A) (Syn.shift B) (var 0) hs.wk hi)
  simpa only [Δ,Syn.shift,subst_normalized,QuadraticTowerCoefficients.subst_width,
    QuadraticTowerScalarBudget.subst_codeCap] using b

theorem radix_at (S A i : PTm n) : Γ ⊢[PRAAx] inst2 radixBody i (data S A) ≐ S := by
  simpa [radixBody,inst2,data] using fst_pair (Γ := Γ) S A
theorem vector_at (S A i : PTm n) : Γ ⊢[PRAAx] inst2 vectorBody i (data S A) ≐ entry A i := by
  simp only [vectorBody,inst2,Foundations.MasterCertificate.subst_entry,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact entry_congr (snd_pair _ _) (.eqRefl _)
theorem places (S A i : PTm n) : Γ ⊢[PRAAx] MixedRadix.Pl radixBody i (data S A) ≐ pw S i := by
  refine prod_const_of _ _ _ _ (.allI (.impI ?_))
  simpa only [Syn.shift,subst_data] using radix_at (Γ := lt (var 0) (Syn.shift i) :: Γ.map Fm.shift)
    (Syn.shift S) (Syn.shift A) (var 0)
theorem packed_bound (A W S : PTm n) (ha : Γ ⊢[PRAAx] boundedEntries A W S) :
    Γ ⊢[PRAAx] lt (packed A W S) (pw S W) := by
  have digits : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift W) ⟶
      lt (inst2 vectorBody (var 0) (Syn.shift (data S A))) (inst2 radixBody (var 0) (Syn.shift (data S A)))) := by
    have hs : Γ.map Fm.shift ⊢[PRAAx] boundedEntries (Syn.shift A) (Syn.shift W) (Syn.shift S) := by
      simpa only [Fm.shift,subst_boundedEntries,Syn.shift] using ha.shift
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_data] using lt_congr (vector_at _ _ _).eqSymm (radix_at _ _ _).eqSymm
      (bounded_at (Syn.shift A) (Syn.shift W) (Syn.shift S) (var 0) hs.wk Prf.hyp0)
  exact lt_congr (.eqRefl _) (places S A W) (MixedRadix.code_lt _ _ _ _ digits)

theorem packed_digit (A W S i : PTm n) (ha : Γ ⊢[PRAAx] boundedEntries A W S)
    (hi : Γ ⊢[PRAAx] lt i W) : Γ ⊢[PRAAx] digit S (packed A W S) i ≐ entry A i := by
  let t := monus W (succ i)
  have span : Γ ⊢[PRAAx] succ i+t ≐ W := (eq_add_of_le hi).eqSymm
  have digits : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ i+t)) ⟶
      lt (inst2 vectorBody (var 0) (Syn.shift (data S A))) (inst2 radixBody (var 0) (Syn.shift (data S A)))) := by
    have hs : Γ.map Fm.shift ⊢[PRAAx] boundedEntries (Syn.shift A) (Syn.shift W) (Syn.shift S) := by
      simpa only [Fm.shift,subst_boundedEntries,Syn.shift] using ha.shift
    have ss : Γ.map Fm.shift ⊢[PRAAx] Syn.shift (succ i+t) ≐ Syn.shift W := by
      simpa only [Fm.shift,Fm.subst_eq,Syn.shift] using span.shift
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_data] using lt_congr (vector_at _ _ _).eqSymm (radix_at _ _ _).eqSymm
      (bounded_at (Syn.shift A) (Syn.shift W) (Syn.shift S) (var 0) hs.wk
        (lt_congr (.eqRefl _) ss.wk Prf.hyp0))
  have ce : Γ ⊢[PRAAx] MixedRadix.Cd radixBody vectorBody (succ i+t) (data S A) ≐ packed A W S :=
    congrAp2 (sumF (MixedRadix.dP radixBody vectorBody)) span (.eqRefl _)
  exact (congrAp2 remF (congrAp2 quoF ce (places S A i)) (radix_at S A i)).eqSymm.eqTrans
    ((MixedRadix.decode digits).eqTrans (vector_at _ _ _))

theorem digit_body_at (S w i : PTm n) : Γ ⊢[PRAAx] inst2 digitBody i (data S w) ≐ digit S w i := by
  simp only [digitBody,inst2,subst_digit,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrAp2 remF (congrAp2 quoF (snd_pair _ _) (congrAp2 powF (.eqRefl _) (fst_pair _ _))) (fst_pair _ _)
theorem decoded_length (W S w : PTm n) : Γ ⊢[PRAAx] length (decoded W S w) ≐ W := sequence_length _ _ _
theorem decoded_lookup (W S w i : PTm n) (hi : Γ ⊢[PRAAx] lt i W) :
    Γ ⊢[PRAAx] entry (decoded W S w) i ≐ digit S w i :=
  (sequence_decode digitBody (x := data S w) hi).eqTrans (digit_body_at _ _ _)

theorem code_bound (h A B : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A B) :
    Γ ⊢[PRAAx] lt (code h A B) (horizon h B) := packed_bound _ _ _ (normalized_bounded h A B ha)
theorem restored_length (h A B : PTm n) : Γ ⊢[PRAAx] length (restored h A B) ≐ width h := decoded_length _ _ _
theorem restored_entry (h A B i : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A B)
    (hi : Γ ⊢[PRAAx] lt i (width h)) :
    Γ ⊢[PRAAx] entry (restored h A B) i ≐ RationalArithmetic.recode (entry A i) :=
  (decoded_lookup _ _ _ _ hi).eqTrans
    ((packed_digit _ _ _ _ (normalized_bounded h A B ha) hi).eqTrans (normalized_lookup h A i hi))
theorem restored_value (h A B i : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A B)
    (hi : Γ ⊢[PRAAx] lt i (width h)) :
    Γ ⊢[PRAAx] rationalEq (entry (restored h A B) i) (entry A i) :=
  rationalEq_congr (restored_entry h A B i ha hi).eqSymm (.eqRefl _) (RationalArithmetic.recode_equal _)
theorem restored_canonical (h A B i : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A B)
    (hi : Γ ⊢[PRAAx] lt i (width h)) :
    Γ ⊢[PRAAx] RationalNormalForm.wellFormed (entry (restored h A B) i) :=
  RationalArithmetic.guard_congr (restored_entry h A B i ha hi) (RationalArithmetic.recode_guard _)

def output (h A B : PTm n) : PTm n := pairT (code h A B)
  (pairT (horizon h B) (pairT (normalized h A) (restored h A B)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (h A B : PTm n) : PTm n := ap3 outputF h A B
ipra_subst output
ipra_subst run
theorem program_at (h A B : PTm n) : Γ ⊢[PRAAx] run h A B ≐ output h A B := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![h,A,B]
theorem returned_code (h A B : PTm n) : Γ ⊢[PRAAx] fstT (run h A B) ≐ code h A B :=
  (program_at _ _ _).fstE
theorem returned_horizon (h A B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h A B)) ≐ horizon h B :=
  (program_at _ _ _).sndE.fstE
theorem returned_tail (h A B : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h A B)) ≐ pairT (normalized h A) (restored h A B) :=
  (program_at _ _ _).sndE.sndE
theorem returned_normalized (h A B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h A B))) ≐ normalized h A :=
  (returned_tail _ _ _).fstE
theorem returned_restored (h A B : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h A B))) ≐ restored h A B :=
  (returned_tail _ _ _).sndE
theorem returned_bound (h A B : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A B) :
    Γ ⊢[PRAAx] lt (fstT (run h A B)) (fstT (sndT (run h A B))) :=
  lt_congr (returned_code h A B).eqSymm (returned_horizon h A B).eqSymm (code_bound h A B ha)
theorem returned_length (h A B : PTm n) :
    Γ ⊢[PRAAx] length (sndT (sndT (sndT (run h A B)))) ≐ width h :=
  (congrFst (returned_restored _ _ _)).eqTrans (restored_length _ _ _)
theorem returned_entry (h A B i : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A B)
    (hi : Γ ⊢[PRAAx] lt i (width h)) :
    Γ ⊢[PRAAx] entry (sndT (sndT (sndT (run h A B)))) i ≐ RationalArithmetic.recode (entry A i) :=
  (entry_congr (returned_restored h A B) (.eqRefl i)).eqTrans (restored_entry h A B i ha hi)

theorem actual_normalized_array_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (normalized (var 0) (var 1)) ≐ width (var 0)) := closeUniv 2 (normalized_length _ _)
theorem actual_normalized_array_entry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (width (var 0)) ⟶ entry (normalized (var 0) (var 1)) (var 2) ≐ RationalArithmetic.recode (entry (var 1) (var 2))) :=
  closeUniv 3 (.impI (normalized_lookup _ _ _ Prf.hyp0))
theorem actual_bounded_array_pack_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (boundedEntries (var 0) (var 1) (var 2) ⟶ lt (packed (var 0) (var 1) (var 2)) (pw (var 2) (var 1))) :=
  closeUniv 3 (.impI (packed_bound _ _ _ Prf.hyp0))
theorem actual_bounded_array_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (boundedEntries (var 0) (var 1) (var 2) ⟶ lt (var 3) (var 1) ⟶
      digit (var 2) (packed (var 0) (var 1) (var 2)) (var 3) ≐ entry (var 0) (var 3)) :=
  closeUniv 4 (.impI (.impI (packed_digit _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_tower_array_horizon_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (arrayHeight (var 0) (var 1) (var 2) ⟶ lt (code (var 0) (var 1) (var 2)) (horizon (var 0) (var 2))) :=
  closeUniv 3 (.impI (code_bound _ _ _ Prf.hyp0))
theorem actual_tower_array_roundtrip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (arrayHeight (var 0) (var 1) (var 2) ⟶ lt (var 3) (width (var 0)) ⟶
      entry (restored (var 0) (var 1) (var 2)) (var 3) ≐ RationalArithmetic.recode (entry (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (restored_entry _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_tower_array_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (arrayHeight (var 0) (var 1) (var 2) ⟶ lt (var 3) (width (var 0)) ⟶
      rationalEq (entry (restored (var 0) (var 1) (var 2)) (var 3)) (entry (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (restored_value _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_tower_array_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (arrayHeight (var 0) (var 1) (var 2) ⟶ lt (var 3) (width (var 0)) ⟶
      RationalNormalForm.wellFormed (entry (restored (var 0) (var 1) (var 2)) (var 3))) :=
  closeUniv 4 (.impI (.impI (restored_canonical _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_array_codec_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_array_horizon_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (arrayHeight (var 0) (var 1) (var 2) ⟶ lt (fstT (run (var 0) (var 1) (var 2))) (fstT (sndT (run (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (returned_bound _ _ _ Prf.hyp0))
theorem actual_returned_array_entry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (arrayHeight (var 0) (var 1) (var 2) ⟶ lt (var 3) (width (var 0)) ⟶
      entry (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) (var 3) ≐ RationalArithmetic.recode (entry (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (returned_entry _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticTowerArrayCodec
