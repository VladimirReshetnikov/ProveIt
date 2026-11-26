import IPRADerivations.Foundations.RuntimeWordAppend
import IPRADerivations.Foundations.FiniteFiberGrouping
import IPRADerivations.Foundations.GuardedTotalization
import IPRADerivations.Core.SubstCommand

/-!
# A cyclic permutation and its wrap bit

The residue and quotient of `j+k` by `m` give the row and wrap bit
for the superelliptic multiplication matrix. All numerical dimensions,
shift amounts and positions are terms of the object theory.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.RuntimeCyclicPermutation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ)
open scoped Fm
open Syn

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rotation (m k j : PTm n) : PTm n := rem (j + k) m
def wrap (m k j : PTm n) : PTm n := quo (j + k) m

ipra_subst rotation

ipra_subst wrap

theorem rotation_spec (m k j : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] (j + k ≐ m * wrap m k j + rotation m k j) ⋏ lt (rotation m k j) m :=
  RuntimeWordAppend.divide_spec m (j + k) hm

theorem rotation_unwrapped (m k j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] lt (j + k) m) :
    Γ ⊢[PRAAx] (wrap m k j ≐ zero) ⋏ (rotation m k j ≐ j + k) :=
  RuntimeWordAppend.divide_unique m (j + k) zero (j + k) hm (by ipra_ring) h

theorem cancel_left_strict {a b c : PTm n} (h : Γ ⊢[PRAAx] lt (a + b) (a + c)) :
    Γ ⊢[PRAAx] lt b c := by
  have hh : Γ ⊢[PRAAx] le (succ b + a) (c + a) :=
    le_congr (by ipra_ring) (add_comm _ _) h
  exact le_of_add_le_add_right hh

theorem sum_below_twice (m k j : PTm n)
    (hk : Γ ⊢[PRAAx] lt k m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] lt (j + k) (m + m) :=
  lt_of_le_of_lt (add_le_add_right k (le_of_lt hj)) (SequenceComposition.add_lt_left m hk)

theorem rotation_wrapped (m k j : PTm n) (hk : Γ ⊢[PRAAx] lt k m)
    (hj : Γ ⊢[PRAAx] lt j m) (h : Γ ⊢[PRAAx] le m (j + k)) :
    Γ ⊢[PRAAx] (wrap m k j ≐ one) ⋏ (rotation m k j ≐ monus (j + k) m) := by
  have hm : Γ ⊢[PRAAx] le one m := lt_of_le_of_lt (zero_le j) hj
  have e := eq_add_of_le h
  have hr : Γ ⊢[PRAAx] lt (monus (j + k) m) m :=
    cancel_left_strict (lt_congr e (.eqRefl _) (sum_below_twice m k j hk hj))
  exact RuntimeWordAppend.divide_unique _ _ _ _ hm (e.eqTrans (by ipra_ring)) hr

theorem wrap_cases (m k j : PTm n) (hk : Γ ⊢[PRAAx] lt k m) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] (wrap m k j ≐ zero) ⋎ (wrap m k j ≐ one) := by
  have hm : Γ ⊢[PRAAx] le one m := lt_of_le_of_lt (zero_le j) hj
  refine .orE (lt_or_le (j + k) m) ?_ ?_
  · exact .orI₁ (.andE₁ (rotation_unwrapped _ _ _ hm.wk Prf.hyp0))
  · exact .orI₂ (.andE₁ (rotation_wrapped _ _ _ hk.wk hj.wk Prf.hyp0))

/-- Equal wrapped residues have equal positions when the two wrap bits agree. -/
theorem inject_same_wrap (m k i j : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hr : Γ ⊢[PRAAx] rotation m k i ≐ rotation m k j)
    (hw : Γ ⊢[PRAAx] wrap m k i ≐ wrap m k j) : Γ ⊢[PRAAx] i ≐ j :=
  add_right_cancel ((Prf.andE₁ (rotation_spec m k i hm)).eqTrans
    ((congrAdd (congrMul (.eqRefl _) hw) hr).eqTrans
      (Prf.andE₁ (rotation_spec m k j hm)).eqSymm))

/-- A position with wrap bit one would exceed the range if its residue also
occurred at a position with wrap bit zero. -/
theorem inject_cross_wrap (m k i j : PTm n) (hj : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] rotation m k i ≐ rotation m k j)
    (hi0 : Γ ⊢[PRAAx] wrap m k i ≐ zero)
    (hj1 : Γ ⊢[PRAAx] wrap m k j ≐ one) : Γ ⊢[PRAAx] Fm.bot := by
  have hm : Γ ⊢[PRAAx] le one m := lt_of_le_of_lt (zero_le j) hj
  have v : Γ ⊢[PRAAx] i+k ≐ rotation m k i :=
    (Prf.andE₁ (rotation_spec m k i hm)).eqTrans
      ((congrAdd (congrMul (.eqRefl _) hi0) (.eqRefl _)).eqTrans (by ipra_ring))
  have u : Γ ⊢[PRAAx] j+k ≐ (m+i)+k :=
    (Prf.andE₁ (rotation_spec m k j hm)).eqTrans
      ((congrAdd (congrMul (.eqRefl _) hj1) (hr.eqSymm.eqTrans v.eqSymm)).eqTrans (by ipra_ring))
  exact le_lt_absurd _ (le_congr (.eqRefl _) (add_right_cancel u).eqSymm (le_add_right m i)) hj

theorem rotation_injective (m k i j : PTm n) (hk : Γ ⊢[PRAAx] lt k m)
    (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] rotation m k i ≐ rotation m k j) : Γ ⊢[PRAAx] i ≐ j := by
  have hm : Γ ⊢[PRAAx] le one m := lt_of_le_of_lt (zero_le i) hi
  refine .orE (wrap_cases m k i hk hi) ?_ ?_
  · refine .orE (wrap_cases m k j hk.wk hj.wk) ?_ ?_
    · exact inject_same_wrap _ _ _ _ hm.wk.wk hr.wk.wk (Prf.hyp1.eqTrans Prf.hyp0.eqSymm)
    · exact .botE _ (inject_cross_wrap _ _ _ _ hj.wk.wk hr.wk.wk Prf.hyp1 Prf.hyp0)
  · refine .orE (wrap_cases m k j hk.wk hj.wk) ?_ ?_
    · exact .botE _ (inject_cross_wrap _ _ _ _ hi.wk.wk hr.wk.wk.eqSymm Prf.hyp0 Prf.hyp1)
    · exact inject_same_wrap _ _ _ _ hm.wk.wk hr.wk.wk (Prf.hyp1.eqTrans Prf.hyp0.eqSymm)

open MasterCertificate (entry sequence sequence_decode sequence_length subst_sequence)
open SequenceComposition (length)

def rotationBody : PTm 2 := rotation (fstT (var 1)) (sndT (var 1)) (var 0)
def rotationTable (m k : PTm n) : PTm n := sequence rotationBody m (pairT m k)
def rotationCode (m k : PTm n) : PTm n := RuntimePermutationWords.encode (rotationTable m k) m

ipra_subst rotationTable

theorem rotation_lookup (m k i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) :
    Γ ⊢[PRAAx] entry (rotationTable m k) i ≐ rotation m k i := by
  refine (sequence_decode rotationBody hi).eqTrans ?_
  simp only [rotationBody,inst2,subst_rotation,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  unfold rotation
  exact congrAp2 remF (congrAdd (.eqRefl _) (snd_pair _ _)) (fst_pair _ _)

theorem rotation_table_range (m k : PTm n) : Γ ⊢[PRAAx] RuntimePermutationWords.range (rotationTable m k) m := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
  have hm : Δ ⊢[PRAAx] le one (Syn.shift m) := lt_of_le_of_lt (zero_le _) hi
  have h := lt_congr (rotation_lookup _ (Syn.shift k) _ hi).eqSymm (.eqRefl _)
    (Prf.andE₂ (rotation_spec _ (Syn.shift k) _ hm))
  simpa only [Δ,Syn.shift,subst_rotationTable] using h

theorem rotation_distinct (m k : PTm n) (hk : Γ ⊢[PRAAx] lt k m) :
    Γ ⊢[PRAAx] RuntimePermutationWords.distinct (rotationTable m k) m := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (var 1) :: (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift).map Fm.shift
  let m₂ := Syn.shift (Syn.shift m)
  let k₂ := Syn.shift (Syn.shift k)
  have hi : Δ ⊢[PRAAx] lt (var 1) m₂ := by
    simpa only [Δ,m₂,List.map_cons,Fm.shift,subst_lt,Syn.subst_var,Syn.shift,Fin.succ_zero_eq_one] using
      (Prf.hyp1 : Δ ⊢[PRAAx] Fm.shift (lt (var 0) (Syn.shift m)))
  have hj : Δ ⊢[PRAAx] lt (var 0) (var 1) := Prf.hyp0
  have hks : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] lt k₂ m₂ := by
    simpa only [k₂,m₂,Fm.shift,subst_lt,Syn.shift] using hk.shift.shift
  have hk₂ : Δ ⊢[PRAAx] lt k₂ m₂ := by
    simp only [Δ,List.map_cons]
    exact hks.wk.wk
  have hjm := lt_of_lt_of_le hj (le_of_lt hi)
  have ei := rotation_lookup m₂ k₂ (var 1) hi
  have ej := rotation_lookup m₂ k₂ (var 0) hjm
  have h : Δ ⊢[PRAAx] neg
      (entry (rotationTable m₂ k₂) (var 1) ≐ entry (rotationTable m₂ k₂) (var 0)) := by
    refine .impI ?_
    have e := rotation_injective m₂ k₂ (var 1) (var 0) hk₂.wk hi.wk hjm.wk
      (ei.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans ej.wk))
    exact lt_irrefl (var 0) _ (lt_congr (.eqRefl _) e hj.wk)
  simpa only [Δ,m₂,k₂,Syn.shift,subst_rotationTable,List.map_cons,Fm.shift,subst_lt,
    Syn.subst_var,Fin.succ_zero_eq_one] using h

theorem rotation_tuple (m k : PTm n) (hk : Γ ⊢[PRAAx] lt k m) :
    Γ ⊢[PRAAx] RuntimePermutationWords.tuple (rotationTable m k) m :=
  .andI (sequence_length _ _ _) (.andI (rotation_table_range _ _) (rotation_distinct _ _ hk))

theorem rotation_code_bound (m k : PTm n) :
    Γ ⊢[PRAAx] lt (rotationCode m k) (RuntimePermutationWords.horizon m) :=
  RuntimePermutationWords.encode_bound _ _ (rotation_table_range _ _)

theorem rotation_digit (m k i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) :
    Γ ⊢[PRAAx] RuntimePermutationWords.digit m (rotationCode m k) i ≐ rotation m k i :=
  (RuntimePermutationWords.encode_decode _ _ _ (rotation_table_range _ _) hi).eqTrans
    (rotation_lookup _ _ _ hi)

theorem rotation_listed (m k : PTm n) (hk : Γ ⊢[PRAAx] lt k m) :
    Γ ⊢[PRAAx] lt (RuntimePermutationWords.position (rotationTable m k) m) (RuntimePermutationWords.count m) ⋏
      (entry (RuntimePermutationWords.words m) (RuntimePermutationWords.position (rotationTable m k) m) ≐
        rotationCode m k) :=
  RuntimePermutationWords.listed _ _ (rotation_tuple _ _ hk)

/-- The first wrapped position in the increasing list of positions. -/
def cutoff (m k : PTm n) : PTm n := monus m k

ipra_subst cutoff

theorem cutoff_span (m k : PTm n) (hk : Γ ⊢[PRAAx] le k m) :
    Γ ⊢[PRAAx] m ≐ cutoff m k + k :=
  (eq_add_of_le hk).eqTrans (add_comm _ _)

theorem before_cutoff (m k i : PTm n) (hk : Γ ⊢[PRAAx] lt k m)
    (hi : Γ ⊢[PRAAx] lt i (cutoff m k)) : Γ ⊢[PRAAx] wrap m k i ≐ zero := by
  have e := cutoff_span m k (le_of_lt hk)
  have hb := lt_congr (add_comm _ _) ((add_comm _ _).eqTrans e.eqSymm)
    (SequenceComposition.add_lt_left k hi)
  exact .andE₁ (rotation_unwrapped _ _ _ (lt_of_le_of_lt (zero_le _) hk) hb)

theorem after_cutoff (m k i : PTm n) (hk : Γ ⊢[PRAAx] lt k m)
    (hi : Γ ⊢[PRAAx] lt i k) : Γ ⊢[PRAAx] wrap m k (cutoff m k + i) ≐ one := by
  have e := cutoff_span m k (le_of_lt hk)
  have hb := lt_congr (.eqRefl _) e.eqSymm (SequenceComposition.add_lt_left (cutoff m k) hi)
  have h : Γ ⊢[PRAAx] le m ((cutoff m k + i) + k) :=
    le_congr e.eqSymm (by ipra_ring) (le_add_right (cutoff m k + k) i)
  exact .andE₁ (rotation_wrapped _ _ _ hk hb h)

def wrapBody : PTm 2 := wrap (fstT (var 1)) (sndT (var 1)) (var 0)
def wrapCount (m k : PTm n) : PTm n := ap2 (sumF wrapBody) m (pairT m k)

theorem wrap_body_at (m k i : PTm n) :
    Γ ⊢[PRAAx] inst2 wrapBody i (pairT m k) ≐ wrap m k i := by
  simp only [wrapBody,inst2,subst_wrap,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  unfold wrap
  exact congrAp2 quoF (congrAdd (.eqRefl _) (snd_pair _ _)) (fst_pair _ _)

theorem wrap_offset_at (m k c i : PTm n) :
    Γ ⊢[PRAAx] inst2 (offB wrapBody) i (pairT c (pairT m k)) ≐ wrap m k (c+i) := by
  rw [inst2_offB]
  exact (congrInst2 wrapBody (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans
    (wrap_body_at _ _ _)

/-- The actual wrap fold has as many ones as the amount of rotation. -/
theorem wrap_count (m k : PTm n) (hk : Γ ⊢[PRAAx] lt k m) :
    Γ ⊢[PRAAx] wrapCount m k ≐ k := by
  let c := cutoff m k
  let x := pairT m k
  have left : Γ ⊢[PRAAx] ap2 (sumF wrapBody) c x ≐ zero := by
    apply sum_zero_of_bounded
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (cutoff (Syn.shift m) (Syn.shift k)) :: Γ.map Fm.shift
    have hks : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift k) (Syn.shift m) := by
      simpa only [Fm.shift,subst_lt,Syn.shift] using hk.shift
    have e : Δ ⊢[PRAAx] inst2 wrapBody (var 0) (pairT (Syn.shift m) (Syn.shift k)) ≐ zero :=
      (wrap_body_at _ _ _).eqTrans (before_cutoff _ _ _ hks.wk Prf.hyp0)
    simpa only [Δ,x,c,Syn.shift,subst_pairT,subst_cutoff] using e
  have right : Γ ⊢[PRAAx] ap2 (sumF (offB wrapBody)) k (pairT c x) ≐ k := by
    refine (sum_congr_bounded _ (one : PTm 2) _ x k ?_).eqTrans
      (FiniteFiberGrouping.sum_units _ _)
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift k) :: Γ.map Fm.shift
    have hks : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift k) (Syn.shift m) := by
      simpa only [Fm.shift,subst_lt,Syn.shift] using hk.shift
    have e : Δ ⊢[PRAAx] inst2 (offB wrapBody) (var 0)
      (pairT (cutoff (Syn.shift m) (Syn.shift k)) (pairT (Syn.shift m) (Syn.shift k))) ≐ one :=
      (wrap_offset_at _ _ _ _).eqTrans (after_cutoff _ _ _ hks.wk Prf.hyp0)
    have hOne : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (pairT (Syn.shift m) (Syn.shift k)) = one := by
      simp [inst2]
    have v : Δ ⊢[PRAAx] inst2 (one : PTm 2) (var 0) (pairT (Syn.shift m) (Syn.shift k)) ≐ one := by
      rw [hOne]
      exact .eqRefl _
    simpa only [Δ,c,x,Syn.shift,subst_pairT,subst_cutoff] using e.eqTrans v.eqSymm
  unfold wrapCount
  refine (congrAp2 (sumF wrapBody) (cutoff_span m k (le_of_lt hk)) (.eqRefl _)).eqTrans ?_
  exact (sum_split wrapBody c k x).eqTrans ((congrAdd left right).eqTrans (zero_add k))

ipra_subst rotationCode

ipra_subst wrapCount

theorem rotation_checker (m k : PTm n) (hk : Γ ⊢[PRAAx] lt k m) :
    Γ ⊢[PRAAx] RuntimePermutationWords.permutationBit m (rotationCode m k) ≐ one :=
  (RuntimePermutationWords.checker_reflection _ _).iffMpr
    (RuntimePermutationWords.encoded_tuple _ _ (rotation_tuple _ _ hk))

/-- Equality with the residue at every position determines the in-range word code. -/
def matchesRotation (m k w : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶
    RuntimePermutationWords.digit (Syn.shift m) (Syn.shift w) (var 0) ≐
      rotation (Syn.shift m) (Syn.shift k) (var 0))

ipra_subst matchesRotation [Syn.subst_shift, Syn.shift_subst]

theorem matches_at (m k w i : PTm n) (h : Γ ⊢[PRAAx] matchesRotation m k w)
    (hi : Γ ⊢[PRAAx] lt i m) :
    Γ ⊢[PRAAx] RuntimePermutationWords.digit m w i ≐ rotation m k i := by
  have rule : Γ ⊢[PRAAx] lt i m ⟶ RuntimePermutationWords.digit m w i ≐ rotation m k i := by
    simpa only [matchesRotation,Fm.subst_imp,Fm.subst_eq,subst_lt,RuntimePermutationWords.subst_digit,
      subst_rotation,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE rule hi

theorem rotation_unique (m k w : PTm n)
    (hw : Γ ⊢[PRAAx] lt w (RuntimePermutationWords.horizon m))
    (h : Γ ⊢[PRAAx] matchesRotation m k w) :
    Γ ⊢[PRAAx] w ≐ rotationCode m k := by
  apply RuntimePermutationWords.word_unique _ _ _ hw (rotation_code_bound m k)
  refine .allI (.impI ?_)
  let m' := Syn.shift m
  let k' := Syn.shift k
  let w' := Syn.shift w
  let i : PTm (n + 1) := var 0
  let Δ := lt i m' :: Γ.map Fm.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] matchesRotation m' k' w' := by
    simpa only [Fm.shift,m',k',w',Syn.shift,subst_matchesRotation] using h.shift
  have hi : Δ ⊢[PRAAx] lt i m' := Prf.hyp0
  have e := (RuntimePermutationWords.word_lookup m' w' i hi).eqTrans
    ((matches_at m' k' w' i hs.wk hi).eqTrans
      ((RuntimePermutationWords.word_lookup m' (rotationCode m' k') i hi).eqTrans
        (rotation_digit _ _ _ hi)).eqSymm)
  simpa only [Δ,i,m',k',w',Syn.shift,RuntimePermutationWords.subst_word,subst_rotationCode] using e

theorem actual_rotation_spec_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶
      ((var 2) + (var 1) ≐ (var 0) * wrap (var 0) (var 1) (var 2) + rotation (var 0) (var 1) (var 2)) ⋏
      lt (rotation (var 0) (var 1) (var 2)) (var 0)) :=
  closeUniv 3 (.impI (rotation_spec _ _ _ Prf.hyp0))

theorem actual_rotation_digit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 0) ⟶ RuntimePermutationWords.digit (var 0) (rotationCode (var 0) (var 1)) (var 2) ≐
      rotation (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (rotation_digit _ _ _ Prf.hyp0))

theorem actual_rotation_retained_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (var 0) ⟶
      lt (RuntimePermutationWords.position (rotationTable (var 0) (var 1)) (var 0))
        (RuntimePermutationWords.count (var 0)) ⋏
      (entry (RuntimePermutationWords.words (var 0))
        (RuntimePermutationWords.position (rotationTable (var 0) (var 1)) (var 0)) ≐ rotationCode (var 0) (var 1))) :=
  closeUniv 2 (.impI (rotation_listed _ _ Prf.hyp0))

theorem actual_wrap_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (var 0) ⟶ wrapCount (var 0) (var 1) ≐ var 1) :=
  closeUniv 2 (.impI (wrap_count _ _ Prf.hyp0))

theorem actual_rotation_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (RuntimePermutationWords.horizon (var 0)) ⟶
      matchesRotation (var 0) (var 1) (var 2) ⟶ var 2 ≐ rotationCode (var 0) (var 1)) :=
  closeUniv 3 (.impI (.impI (rotation_unique _ _ _ Prf.hyp1 Prf.hyp0)))

/-- The original column whose forward cyclic image is the requested row. -/
def inverseIndex (m k r : PTm n) : PTm n :=
  GuardedTotalization.sel (Signum.sg (monus k r)) (cutoff m k + r) (monus r k)

ipra_subst inverseIndex [GuardedTotalization.sel, Signum.sg]

theorem inverse_small_row (m k r : PTm n)
    (hk : Γ ⊢[PRAAx] lt k m) (hrk : Γ ⊢[PRAAx] lt r k) : Γ ⊢[PRAAx]
    lt (inverseIndex m k r) m ⋏
      ((rotation m k (inverseIndex m k r) ≐ r) ⋏ (wrap m k (inverseIndex m k r) ≐ one)) := by
  have ix : Γ ⊢[PRAAx] inverseIndex m k r ≐ cutoff m k + r :=
    GuardedTotalization.sel_one (AnalyticNumberTheory.Totatives.sg_lt hrk)
  have es := cutoff_span m k (le_of_lt hk)
  have hm : Γ ⊢[PRAAx] le one m := lt_of_le_of_lt (zero_le _) hk
  have hr : Γ ⊢[PRAAx] lt r m := lt_of_lt_of_le hrk (le_of_lt hk)
  have hb := lt_congr ix.eqSymm es.eqSymm (SequenceComposition.add_lt_left (cutoff m k) hrk)
  have e : Γ ⊢[PRAAx] inverseIndex m k r + k ≐ m * one + r :=
    (congrAdd ix (.eqRefl _)).eqTrans ((by ipra_ring :
      Γ ⊢[PRAAx] (cutoff m k + r) + k ≐ (cutoff m k + k) + r).eqTrans
      ((congrAdd es.eqSymm (.eqRefl _)).eqTrans (by ipra_ring)))
  have d := RuntimeWordAppend.divide_unique m (inverseIndex m k r + k) one r hm e hr
  exact .andI hb (.andI (.andE₂ d) (.andE₁ d))

theorem inverse_large_row (m k r : PTm n)
    (hr : Γ ⊢[PRAAx] lt r m) (hkr : Γ ⊢[PRAAx] le k r) : Γ ⊢[PRAAx]
    lt (inverseIndex m k r) m ⋏
      ((rotation m k (inverseIndex m k r) ≐ r) ⋏ (wrap m k (inverseIndex m k r) ≐ zero)) := by
  have ix : Γ ⊢[PRAAx] inverseIndex m k r ≐ monus r k :=
    GuardedTotalization.sel_zero (AnalyticNumberTheory.Totatives.sg_le hkr)
  have es := eq_add_of_le hkr
  have hb : Γ ⊢[PRAAx] le (monus r k) r :=
    le_congr (.eqRefl _) es.eqSymm (le_add_left (monus r k) k)
  have hi := lt_congr ix.eqSymm (.eqRefl _) (lt_of_le_of_lt hb hr)
  have hm : Γ ⊢[PRAAx] le one m := lt_of_le_of_lt (zero_le _) hr
  have e : Γ ⊢[PRAAx] inverseIndex m k r + k ≐ m * zero + r :=
    (congrAdd ix (.eqRefl _)).eqTrans ((add_comm _ _).eqTrans (es.eqSymm.eqTrans (by ipra_ring)))
  have d := RuntimeWordAppend.divide_unique m (inverseIndex m k r + k) zero r hm e hr
  exact .andI hi (.andI (.andE₂ d) (.andE₁ d))

theorem inverse_correct (m k r : PTm n)
    (hk : Γ ⊢[PRAAx] lt k m) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    lt (inverseIndex m k r) m ⋏ (rotation m k (inverseIndex m k r) ≐ r) := by
  refine .orE (lt_or_le r k) ?_ ?_
  · have h := inverse_small_row m k r hk.wk Prf.hyp0
    exact .andI (.andE₁ h) (.andE₁ (.andE₂ h))
  · have h := inverse_large_row m k r hr.wk Prf.hyp0
    exact .andI (.andE₁ h) (.andE₁ (.andE₂ h))

theorem inverse_rotation (m k j : PTm n)
    (hk : Γ ⊢[PRAAx] lt k m) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] inverseIndex m k (rotation m k j) ≐ j := by
  have hm : Γ ⊢[PRAAx] le one m := lt_of_le_of_lt (zero_le _) hj
  have h := inverse_correct m k (rotation m k j) hk (.andE₂ (rotation_spec m k j hm))
  exact rotation_injective _ _ _ _ hk (.andE₁ h) hj (.andE₂ h)

theorem actual_inverse_correct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶ lt (var 2) (var 0) ⟶
      lt (inverseIndex (var 0) (var 1) (var 2)) (var 0) ⋏
      rotation (var 0) (var 1) (inverseIndex (var 0) (var 1) (var 2)) ≐ var 2) :=
  closeUniv 3 (.impI (.impI (inverse_correct _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.RuntimeCyclicPermutation
