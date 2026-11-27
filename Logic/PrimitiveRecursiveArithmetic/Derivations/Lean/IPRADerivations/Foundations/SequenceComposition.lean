import IPRADerivations.Foundations.MasterCertificate
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual sequence append and runtime demand flattening

Sequences use the checked length/reverse-stack encoding of
`MasterCertificate`. Append re-encodes the selected entries in a genuine
primitive-recursive sequence. Flattening is a primitive-recursive fold of
append over the decoded outer queries. All lengths and indices are internal;
empty sequences and empty inner blocks require no special assumptions.

These are the finite list-arithmetic prerequisites for the FIBER composition
theorem. The full certificate composition theorem is not asserted here.
-/

namespace LeanProofs.IPRA.Foundations.SequenceComposition

open_ipra exports
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry sequence_length sequence_decode)
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def length (a : PTm n) : PTm n := fstT a
def empty : PTm n := pairT zero zero

ipra_subst length
@[simp] theorem subst_empty {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (empty : PTm n) = (empty : PTm m) := by simp [empty]

theorem empty_length : Γ ⊢[PRAAx] length (empty : PTm n) ≐ zero := fst_pair _ _

theorem entry_congr {a b i j : PTm n} (hab : Γ ⊢[PRAAx] a ≐ b) (hij : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] entry a i ≐ entry b j := by
  have h := Prf.eqCongr (entry (var 0) (var 1) : PTm 2)
    (σ := ![a, i]) (σ' := ![b, j]) (fun k => by fin_cases k <;> assumption)
  simpa only [MasterCertificate.subst_entry, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one] using h

def appendValue (a b i : PTm n) : PTm n :=
  sg (monus (length a) i) * entry a i +
    monus one (sg (monus (length a) i)) * entry b (monus i (length a))

ipra_subst appendValue [sg]

def appendBody : PTm 2 := appendValue (fstT (var 1)) (sndT (var 1)) (var 0)

def append (a b : PTm n) : PTm n :=
  sequence appendBody (length a + length b) (pairT a b)

ipra_subst append

theorem append_length (a b : PTm n) :
    Γ ⊢[PRAAx] length (append a b) ≐ length a + length b := sequence_length _ _ _

theorem append_value_at (a b i : PTm n) :
    Γ ⊢[PRAAx] inst2 appendBody i (pairT a b) ≐ appendValue a b i := by
  ipra_congr (appendValue (var 0) (var 1) (var 2) : PTm 3) with
    [fst_pair _ _, snd_pair _ _, .eqRefl i] using [inst2, appendBody]

theorem append_lookup {a b i : PTm n} (hi : Γ ⊢[PRAAx] lt i (length a + length b)) :
    Γ ⊢[PRAAx] entry (append a b) i ≐ appendValue a b i :=
  (sequence_decode appendBody hi).eqTrans (append_value_at _ _ _)

theorem append_left {a b i : PTm n} (hi : Γ ⊢[PRAAx] lt i (length a)) :
    Γ ⊢[PRAAx] entry (append a b) i ≐ entry a i := by
  refine (append_lookup (lt_of_lt_of_le hi (le_add_right _ _))).eqTrans ?_
  unfold appendValue
  ipra_lc 𝔞(entry a i) * natEq (sg_lt hi) +
    𝔞(entry b (monus i (length a))) * natEq ((congrMonus (Γ := Γ) (.eqRefl one) (sg_lt hi)).eqTrans (monus_self one))

theorem append_right_at {a b i : PTm n} (ha : Γ ⊢[PRAAx] le (length a) i)
    (hi : Γ ⊢[PRAAx] lt i (length a + length b)) :
    Γ ⊢[PRAAx] entry (append a b) i ≐ entry b (monus i (length a)) := by
  refine (append_lookup hi).eqTrans ?_
  unfold appendValue
  ipra_lc 𝔞(entry a i) * natEq (sg_le ha) +
    𝔞(entry b (monus i (length a))) * natEq ((congrMonus (Γ := Γ) (.eqRefl one) (sg_le ha)).eqTrans (monus_zero one))

theorem add_lt_left (a : PTm n) {i b : PTm n} (hi : Γ ⊢[PRAAx] lt i b) :
    Γ ⊢[PRAAx] lt (a + i) (a + b) :=
  le_congr (by ipra_ring) (add_comm _ _) (add_le_add_right a hi)

theorem append_right {a b i : PTm n} (hi : Γ ⊢[PRAAx] lt i (length b)) :
    Γ ⊢[PRAAx] entry (append a b) (length a + i) ≐ entry b i :=
  (append_right_at (le_add_right _ _) (add_lt_left _ hi)).eqTrans
    (entry_congr (.eqRefl _) (add_monus' _ _))

#print axioms append_left
#print axioms append_right

/-! ## Runtime blocks, prefixSum sums, and an actual append fold -/

def block (inner : PR 2) (outer x j : PTm n) : PTm n := ap2 inner (entry outer j) x

ipra_subst block

/-- Variables `0=j`, `1=outer`, `2=x`. -/
def lengthBody (inner : PR 2) : PTm 3 := length (block inner (var 1) (var 2) (var 0))

def prefixSum (inner : PR 2) (outer x j : PTm n) : PTm n := ap3 (sum2F (lengthBody inner)) j outer x

@[simp] theorem subst_prefix {m : ℕ} (σ : Fin n → PTm m) (inner : PR 2) (outer x j : PTm n) :
    Syn.subst σ (prefixSum inner outer x j) =
      prefixSum inner (Syn.subst σ outer) (Syn.subst σ x) (Syn.subst σ j) := by simp [prefixSum]

theorem prefix_zero (inner : PR 2) (outer x : PTm n) :
    Γ ⊢[PRAAx] prefixSum inner outer x zero ≐ zero := sum2_zero _ _ _

theorem prefix_succ (inner : PR 2) (outer x j : PTm n) :
    Γ ⊢[PRAAx] prefixSum inner outer x (succ j) ≐
      prefixSum inner outer x j + length (block inner outer x j) := by
  simpa [prefixSum, lengthBody, inst3] using sum2_succ (Γ := Γ) (lengthBody inner) j outer x

/-- Variables `0=j`, `1=previous`, `2=outer`, `3=x`. -/
def foldStep (inner : PR 2) : PTm 4 := append (var 1) (block inner (var 2) (var 3) (var 0))
def foldF (inner : PR 2) : PR 3 := recDef empty (foldStep inner)
def fold (inner : PR 2) (outer x j : PTm n) : PTm n := ap3 (foldF inner) j outer x

ipra_subst fold

theorem fold_zero (inner : PR 2) (outer x : PTm n) :
    Γ ⊢[PRAAx] fold inner outer x zero ≐ empty := by
  simpa only [fold, foldF, ap3, subst_empty]
    using rec_zero_vecCons (Γ := Γ) (empty : PTm 2) (foldStep inner) ![outer, x]

theorem fold_succ (inner : PR 2) (outer x j : PTm n) :
    Γ ⊢[PRAAx] fold inner outer x (succ j) ≐ append (fold inner outer x j) (block inner outer x j) := by
  simpa [fold, foldF, ap3, foldStep]
    using rec_succ_vecCons (Γ := Γ) (empty : PTm 2) (foldStep inner) j ![outer, x]

theorem fold_length (inner : PR 2) (outer x j : PTm n) :
    Γ ⊢[PRAAx] length (fold inner outer x j) ≐ prefixSum inner outer x j := by
  have all : Γ ⊢[PRAAx] .all
      (length (fold inner (Syn.shift outer) (Syn.shift x) (var 0)) ≐
        prefixSum inner (Syn.shift outer) (Syn.shift x) (var 0)) := by
    ipra_qfind (trivial) [subst_length, subst_fold, subst_prefix]
    · exact ((congrFst (fold_zero inner outer x)).eqTrans empty_length).eqTrans (prefix_zero _ _ _).eqSymm
    · exact ((congrFst (fold_succ inner _ _ _)).eqTrans (append_length _ _)).eqTrans
        ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (prefix_succ _ _ _ _).eqSymm)
  ipra_simpa_inst [Fm.subst_eq, subst_length, subst_fold, subst_prefix] using Prf.allE j all

theorem prefix_add_mono (inner : PR 2) (outer x a k : PTm n) :
    Γ ⊢[PRAAx] le (prefixSum inner outer x a) (prefixSum inner outer x (a + k)) := by
  have all : Γ ⊢[PRAAx] .all
      (le (prefixSum inner (Syn.shift outer) (Syn.shift x) (Syn.shift a))
        (prefixSum inner (Syn.shift outer) (Syn.shift x) (Syn.shift a + var 0))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_prefix]
    · exact le_congr (.eqRefl _) (congrAp3 _ (add_zero a) (.eqRefl outer) (.eqRefl x)).eqSymm (le_refl _)
    · have step : (le (prefixSum inner (Syn.shift outer) (Syn.shift x) (Syn.shift a))
          (prefixSum inner (Syn.shift outer) (Syn.shift x) (Syn.shift a + var 0))) :: Γ.map Fm.shift ⊢[PRAAx]
          le (prefixSum inner (Syn.shift outer) (Syn.shift x) (Syn.shift a + var 0))
            (prefixSum inner (Syn.shift outer) (Syn.shift x) (Syn.shift a + succ (var 0))) := by
        exact le_congr (.eqRefl _)
          (((congrAp3 _ (add_succ _ _) (.eqRefl _) (.eqRefl _)).eqTrans (prefix_succ _ _ _ _)).eqSymm)
          (le_add_right _ _)
      exact le_trans Prf.hyp0 step
  ipra_simpa_inst [subst_le, subst_prefix, PTm.subst_add] using Prf.allE k all

theorem prefix_mono (inner : PR 2) (outer x : PTm n) {a b : PTm n}
    (hab : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (prefixSum inner outer x a) (prefixSum inner outer x b) :=
  le_congr (.eqRefl _) (congrAp3 _ (eq_add_of_le hab).eqSymm (.eqRefl _) (.eqRefl _))
    (prefix_add_mono _ _ _ a (monus b a))

#print axioms fold_length

def lookupCondition (inner : PR 2) (outer x j localIndex count : PTm n) : Fm PTm n :=
  lt j count ⟶ lt localIndex (length (block inner outer x j)) ⟶
    entry (fold inner outer x count) (prefixSum inner outer x j + localIndex) ≐
      entry (block inner outer x j) localIndex

ipra_subst lookupCondition

theorem fold_lookup_step (inner : PR 2) (outer x j localIndex count : PTm n)
    (ih : Γ ⊢[PRAAx] lookupCondition inner outer x j localIndex count)
    (hj : Γ ⊢[PRAAx] lt j (succ count))
    (hl : Γ ⊢[PRAAx] lt localIndex (length (block inner outer x j))) :
    Γ ⊢[PRAAx] entry (fold inner outer x (succ count)) (prefixSum inner outer x j + localIndex) ≐
      entry (block inner outer x j) localIndex := by
  refine .orE (lt_succ_cases hj) ?_ ?_
  · have localBound : (lt j count :: Γ) ⊢[PRAAx]
        lt (prefixSum inner outer x j + localIndex) (prefixSum inner outer x (succ j)) :=
      lt_congr (.eqRefl _) (prefix_succ _ _ _ _).eqSymm (add_lt_left _ hl.wk)
    have prefixBound : (lt j count :: Γ) ⊢[PRAAx]
        lt (prefixSum inner outer x j + localIndex) (prefixSum inner outer x count) :=
      lt_of_lt_of_le localBound (prefix_mono inner outer x Prf.hyp0)
    have storedBound : (lt j count :: Γ) ⊢[PRAAx]
        lt (prefixSum inner outer x j + localIndex) (length (fold inner outer x count)) :=
      lt_congr (.eqRefl _) (fold_length _ _ _ _).eqSymm prefixBound
    exact (entry_congr (fold_succ inner outer x count) (.eqRefl _)).eqTrans
      ((append_left storedBound).eqTrans (.impE (.impE ih.wk Prf.hyp0) hl.wk))
  · have blockEq : ((j ≐ count) :: Γ) ⊢[PRAAx] block inner outer x j ≐ block inner outer x count :=
      congrAp2 inner (entry_congr (.eqRefl _) Prf.hyp0) (.eqRefl x)
    have offsetEq : ((j ≐ count) :: Γ) ⊢[PRAAx]
        prefixSum inner outer x j ≐ length (fold inner outer x count) :=
      (congrAp3 _ Prf.hyp0 (.eqRefl outer) (.eqRefl x)).eqTrans (fold_length _ _ _ _).eqSymm
    have localBound : ((j ≐ count) :: Γ) ⊢[PRAAx]
        lt localIndex (length (block inner outer x count)) := lt_congr (.eqRefl _) (congrFst blockEq) hl.wk
    exact (entry_congr (fold_succ inner outer x count) (congrAdd offsetEq (.eqRefl _))).eqTrans
      ((append_right localBound).eqTrans (entry_congr blockEq.eqSymm (.eqRefl _)))

/-- Lookup at the actual prefix-sum offset of any nonempty block. Empty
blocks are covered by the same statement because their local-index premise is false. -/
theorem fold_lookup (inner : PR 2) (outer x j localIndex count : PTm n)
    (hj : Γ ⊢[PRAAx] lt j count)
    (hl : Γ ⊢[PRAAx] lt localIndex (length (block inner outer x j))) :
    Γ ⊢[PRAAx] entry (fold inner outer x count) (prefixSum inner outer x j + localIndex) ≐
      entry (block inner outer x j) localIndex := by
  have all : Γ ⊢[PRAAx] .all (lookupCondition inner (Syn.shift outer) (Syn.shift x)
      (Syn.shift j) (Syn.shift localIndex) (var 0)) := by
    ipra_qfind (⟨lt_QF _ _, ⟨lt_QF _ _, trivial⟩⟩) [subst_lookupCondition]
    · exact .impI (.impI (lt_zero_absurd _ Prf.hyp1))
    · exact .impI (.impI (fold_lookup_step inner _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))
  have h := Prf.allE count all
  simp only [subst_lookupCondition, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact .impE (.impE h hj) hl

def flatMap (inner : PR 2) (outer x : PTm n) : PTm n := fold inner outer x (length outer)

ipra_subst flatMap

theorem flatMap_length (inner : PR 2) (outer x : PTm n) :
    Γ ⊢[PRAAx] length (flatMap inner outer x) ≐ prefixSum inner outer x (length outer) :=
  fold_length _ _ _ _

theorem flatMap_lookup (inner : PR 2) (outer x j localIndex : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length outer))
    (hl : Γ ⊢[PRAAx] lt localIndex (length (block inner outer x j))) :
    Γ ⊢[PRAAx] entry (flatMap inner outer x) (prefixSum inner outer x j + localIndex) ≐
      entry (block inner outer x j) localIndex := fold_lookup _ _ _ _ _ _ hj hl

theorem flatMap_empty (inner : PR 2) (x : PTm n) :
    Γ ⊢[PRAAx] flatMap inner empty x ≐ empty :=
  (congrAp3 _ empty_length (.eqRefl _) (.eqRefl _)).eqTrans (fold_zero _ _ _)

#print axioms flatMap_length
#print axioms flatMap_lookup

/-! ## Append associativity in the extensional sequence sense -/

theorem offset_lt {a b i : PTm n} (ha : Γ ⊢[PRAAx] le a i)
    (hi : Γ ⊢[PRAAx] lt i (a + b)) : Γ ⊢[PRAAx] lt (monus i a) b := by
  refine le_of_eq_add (d := monus (a + b) (succ i)) ?_
  ipra_lc natEq (eq_add_of_le ha) + natEq (eq_add_of_le hi)

theorem append_assoc_length (a b c : PTm n) :
    Γ ⊢[PRAAx] length (append (append a b) c) ≐ length (append a (append b c)) :=
  ((append_length _ _).eqTrans (congrAdd (append_length _ _) (.eqRefl _))).eqTrans
    ((add_assoc _ _ _).eqTrans
      ((congrAdd (.eqRefl _) (append_length _ _)).eqSymm.eqTrans (append_length _ _).eqSymm))

theorem append_assoc_entry (a b c i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length a + length b + length c)) :
    Γ ⊢[PRAAx] entry (append (append a b) c) i ≐ entry (append a (append b c)) i := by
  have hiL : Γ ⊢[PRAAx] lt i (length (append a b) + length c) :=
    lt_congr (.eqRefl _) (congrAdd (append_length _ _) (.eqRefl _)).eqSymm hi
  have hiR : Γ ⊢[PRAAx] lt i (length a + length (append b c)) :=
    lt_congr (.eqRefl _) ((congrAdd (.eqRefl _) (append_length _ _)).eqTrans
      (add_assoc _ _ _).eqSymm).eqSymm hi
  refine .orE (lt_or_le i (length a)) ?_ ?_
  · have hiAB : (lt i (length a) :: Γ) ⊢[PRAAx] lt i (length (append a b)) :=
      lt_congr (.eqRefl _) (append_length _ _).eqSymm
        (lt_of_lt_of_le Prf.hyp0 (le_add_right _ _))
    exact (append_left hiAB).eqTrans ((append_left Prf.hyp0).eqTrans (append_left Prf.hyp0).eqSymm)
  · have ei : (le (length a) i :: Γ) ⊢[PRAAx] i ≐ length a + monus i (length a) :=
      eq_add_of_le Prf.hyp0
    have hj : (le (length a) i :: Γ) ⊢[PRAAx]
        lt (monus i (length a)) (length b + length c) :=
      offset_lt Prf.hyp0 (lt_congr (.eqRefl _) (add_assoc _ _ _) hi.wk)
    refine .orE (lt_or_le (monus i (length a)) (length b)) ?_ ?_
    · have hiAB : (lt (monus i (length a)) (length b) :: le (length a) i :: Γ) ⊢[PRAAx]
          lt i (length a + length b) := lt_congr ei.wk.eqSymm (.eqRefl _) (add_lt_left _ Prf.hyp0)
      have left := (append_left (b := c) (lt_congr (.eqRefl _) (append_length _ _).eqSymm hiAB)).eqTrans
        (append_right_at Prf.hyp1 hiAB)
      have right := (append_right_at Prf.hyp1 hiR.wk.wk).eqTrans (append_left Prf.hyp0)
      exact left.eqTrans right.eqSymm
    · have hAB : (le (length b) (monus i (length a)) :: le (length a) i :: Γ) ⊢[PRAAx]
          le (length a + length b) i :=
        le_congr (add_comm _ _) ((add_comm _ _).eqTrans ei.wk.eqSymm)
          (add_le_add_right (length a) Prf.hyp0)
      have indexEq : (le (length b) (monus i (length a)) :: le (length a) i :: Γ) ⊢[PRAAx]
          monus i (length (append a b)) ≐ monus (monus i (length a)) (length b) :=
        (congrMonus ei.wk (append_length _ _)).eqTrans
          ((congrMonus (add_comm _ _) (add_comm _ _)).eqTrans (monus_add_add _ _ _))
      have left := (append_right_at
        (le_congr (append_length _ _).eqSymm (.eqRefl _) hAB) hiL.wk.wk).eqTrans
        (entry_congr (.eqRefl _) indexEq)
      have right := (append_right_at Prf.hyp1 hiR.wk.wk).eqTrans (append_right_at Prf.hyp0 hj.wk)
      exact left.eqTrans right.eqSymm

/-! ## Literal flattening and empty blocks -/

def identityInner : PR 2 := .proj 0
def flatten (outer : PTm n) : PTm n := flatMap identityInner outer zero
def flattenedLengthBody : PTm 2 := length (entry (var 1) (var 0))
def flattenedPrefix (outer j : PTm n) : PTm n := ap2 (sumF flattenedLengthBody) j outer

@[simp] theorem subst_flattenedPrefix {m : ℕ} (σ : Fin n → PTm m) (outer j : PTm n) :
    Syn.subst σ (flattenedPrefix outer j) = flattenedPrefix (Syn.subst σ outer) (Syn.subst σ j) :=
  subst_ap2 _ _ _ _

theorem identity_block (outer j : PTm n) :
    Γ ⊢[PRAAx] block identityInner outer zero j ≐ entry outer j := by
  simpa [block, identityInner, ap2] using PRA.proj (Γ := Γ) (0 : Fin 2) ![entry outer j, zero]

theorem identity_prefix (outer j : PTm n) :
    Γ ⊢[PRAAx] prefixSum identityInner outer zero j ≐ flattenedPrefix outer j := by
  have all : Γ ⊢[PRAAx] .all
      (prefixSum identityInner (Syn.shift outer) zero (var 0) ≐ flattenedPrefix (Syn.shift outer) (var 0)) := by
    ipra_qfind (trivial) [subst_prefix, subst_flattenedPrefix]
    · exact (prefix_zero _ _ _).eqTrans (sum_zero _ _).eqSymm
    · refine (prefix_succ _ _ _ _).eqTrans ?_
      refine (congrAdd Prf.hyp0 (congrFst (identity_block _ _))).eqTrans ?_
      simpa [length, flattenedPrefix, flattenedLengthBody, inst2] using
        (sum_succ' (Γ := (prefixSum identityInner (Syn.shift outer) zero (var 0) ≐
          flattenedPrefix (Syn.shift outer) (var 0)) :: Γ.map Fm.shift)
          flattenedLengthBody (var 0) (Syn.shift outer)).eqSymm
  simpa only [Fm.subst_eq, subst_prefix, subst_flattenedPrefix, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] using Prf.allE j all

theorem flatten_length (outer : PTm n) :
    Γ ⊢[PRAAx] length (flatten outer) ≐ flattenedPrefix outer (length outer) :=
  (flatMap_length _ _ _).eqTrans (identity_prefix _ _)

theorem flatten_lookup (outer j localIndex : PTm n) (hj : Γ ⊢[PRAAx] lt j (length outer))
    (hl : Γ ⊢[PRAAx] lt localIndex (length (entry outer j))) :
    Γ ⊢[PRAAx] entry (flatten outer) (flattenedPrefix outer j + localIndex) ≐ entry (entry outer j) localIndex := by
  have localBound := lt_congr (.eqRefl _) (congrFst (identity_block (Γ := Γ) outer j)).eqSymm hl
  exact (entry_congr (.eqRefl _) (congrAdd (identity_prefix _ _).eqSymm (.eqRefl _))).eqTrans
    ((flatMap_lookup _ _ _ _ _ hj localBound).eqTrans (entry_congr (identity_block _ _) (.eqRefl _)))

theorem flatten_empty : Γ ⊢[PRAAx] flatten (empty : PTm n) ≐ empty := flatMap_empty _ _

theorem zero_block_prefix (inner : PR 2) (outer x j : PTm n)
    (hz : Γ ⊢[PRAAx] length (block inner outer x j) ≐ zero) :
    Γ ⊢[PRAAx] prefixSum inner outer x (succ j) ≐ prefixSum inner outer x j :=
  (prefix_succ _ _ _ _).eqTrans ((congrAdd (.eqRefl _) hz).eqTrans (add_zero _))

theorem zero_block_fold_length (inner : PR 2) (outer x j : PTm n)
    (hz : Γ ⊢[PRAAx] length (block inner outer x j) ≐ zero) :
    Γ ⊢[PRAAx] length (fold inner outer x (succ j)) ≐ length (fold inner outer x j) :=
  (fold_length _ _ _ _).eqTrans ((zero_block_prefix _ _ _ _ hz).eqTrans (fold_length _ _ _ _).eqSymm)

#print axioms append_assoc_entry
#print axioms flatten_length
#print axioms flatten_lookup

theorem flatMap_zero_length (inner : PR 2) (outer x : PTm n)
    (hz : Γ ⊢[PRAAx] length outer ≐ zero) :
    Γ ⊢[PRAAx] flatMap inner outer x ≐ empty :=
  (congrAp3 _ hz (.eqRefl _) (.eqRefl _)).eqTrans (fold_zero _ _ _)

theorem flatten_zero_length (outer : PTm n) (hz : Γ ⊢[PRAAx] length outer ≐ zero) :
    Γ ⊢[PRAAx] flatten outer ≐ empty := flatMap_zero_length _ _ _ hz

/-! ## Closed object-theory statements -/

/-- Variables `0=a`, `1=b`, `2=i`. -/
def appendFormula : Fm PTm 3 :=
  (length (append (var 0) (var 1)) ≐ length (var 0) + length (var 1)) ⋏
    ((lt (var 2) (length (var 0)) ⟶
      entry (append (var 0) (var 1)) (var 2) ≐ entry (var 0) (var 2)) ⋏
    (lt (var 2) (length (var 1)) ⟶
      entry (append (var 0) (var 1)) (length (var 0) + var 2) ≐ entry (var 1) (var 2)))

theorem sequence_append : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 appendFormula :=
  closeUniv 3 (.andI (append_length _ _)
    (.andI (.impI (append_left Prf.hyp0)) (.impI (append_right Prf.hyp0))))

/-- Variables `0=a`, `1=b`, `2=c`, `3=i`. Associativity is extensional:
equal stored lengths and equal decoded entries at every valid coordinate. -/
def associativityFormula : Fm PTm 4 :=
  (length (append (append (var 0) (var 1)) (var 2)) ≐
    length (append (var 0) (append (var 1) (var 2)))) ⋏
  (lt (var 3) (length (var 0) + length (var 1) + length (var 2)) ⟶
    entry (append (append (var 0) (var 1)) (var 2)) (var 3) ≐
      entry (append (var 0) (append (var 1) (var 2))) (var 3))

theorem sequence_append_associative :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 associativityFormula :=
  closeUniv 4 (.andI (append_assoc_length _ _ _) (.impI (append_assoc_entry _ _ _ _ Prf.hyp0)))

/-- Variables `0=outer`, `1=x`. The right side is the actual PR sum of
`length(inner(entry outer j,x))` below the runtime stored outer length. -/
def flatMapLengthFormula (inner : PR 2) : Fm PTm 2 :=
  length (flatMap inner (var 0) (var 1)) ≐ prefixSum inner (var 0) (var 1) (length (var 0))

theorem runtime_flatMap_length (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (flatMapLengthFormula inner) :=
  closeUniv 2 (flatMap_length inner _ _)

/-- Variables `0=outer`, `1=x`, `2=j`, `3=localIndex`. -/
def flatMapLookupFormula (inner : PR 2) : Fm PTm 4 :=
  lt (var 2) (length (var 0)) ⟶ lt (var 3) (length (block inner (var 0) (var 1) (var 2))) ⟶
    entry (flatMap inner (var 0) (var 1)) (prefixSum inner (var 0) (var 1) (var 2) + var 3) ≐
      entry (block inner (var 0) (var 1) (var 2)) (var 3)

theorem runtime_flatMap_lookup (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (flatMapLookupFormula inner) :=
  closeUniv 4 (.impI (.impI (flatMap_lookup inner _ _ _ _ Prf.hyp1 Prf.hyp0)))

/-- Variables `0=outer`, `1=j`, `2=localIndex`. -/
def flattenFormula : Fm PTm 3 :=
  (length (flatten (var 0)) ≐ flattenedPrefix (var 0) (length (var 0))) ⋏
  (lt (var 1) (length (var 0)) ⟶ lt (var 2) (length (entry (var 0) (var 1))) ⟶
    entry (flatten (var 0)) (flattenedPrefix (var 0) (var 1) + var 2) ≐
      entry (entry (var 0) (var 1)) (var 2))

theorem runtime_flatten : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 flattenFormula :=
  closeUniv 3 (.andI (flatten_length _) (.impI (.impI (flatten_lookup _ _ _ Prf.hyp1 Prf.hyp0))))

/-- Variables `0=outer`, `1=x`; empty outer codes may have arbitrary payloads. -/
def emptyFormula (inner : PR 2) : Fm PTm 2 :=
  (length (empty : PTm 2) ≐ zero) ⋏
    ((flatMap inner empty (var 1) ≐ empty) ⋏
      ((flatten (empty : PTm 2) ≐ empty) ⋏
        ((length (var 0) ≐ zero) ⟶
          ((flatMap inner (var 0) (var 1) ≐ empty) ⋏ (flatten (var 0) ≐ empty)))))

theorem empty_sequence_composition (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (emptyFormula inner) :=
  closeUniv 2 (.andI empty_length (.andI (flatMap_empty inner _)
    (.andI flatten_empty (.impI (.andI (flatMap_zero_length inner _ _ Prf.hyp0)
      (flatten_zero_length _ Prf.hyp0))))))

/-- Variables `0=outer`, `1=x`, `2=j`. -/
def zeroBlockFormula (inner : PR 2) : Fm PTm 3 :=
  (length (block inner (var 0) (var 1) (var 2)) ≐ zero) ⟶
    ((prefixSum inner (var 0) (var 1) (succ (var 2)) ≐ prefixSum inner (var 0) (var 1) (var 2)) ⋏
      (length (fold inner (var 0) (var 1) (succ (var 2))) ≐ length (fold inner (var 0) (var 1) (var 2))))

theorem zero_length_inner_block (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (zeroBlockFormula inner) :=
  closeUniv 3 (.impI (.andI (zero_block_prefix inner _ _ _ Prf.hyp0)
    (zero_block_fold_length inner _ _ _ Prf.hyp0)))

#print axioms sequence_append
#print axioms sequence_append_associative
#print axioms runtime_flatMap_length
#print axioms runtime_flatMap_lookup
#print axioms runtime_flatten
#print axioms empty_sequence_composition
#print axioms zero_length_inner_block

end LeanProofs.IPRA.Foundations.SequenceComposition

export_ipra Foundations.SequenceComposition (add_lt_left append_left append_right)
