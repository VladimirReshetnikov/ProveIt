import IPRADerivations.Analysis.GaussianRationalSumAlgebra
import IPRADerivations.Foundations.MasterCertificate

/-!
# Actual segments and finite splits of Gaussian-rational sums

Each segment is the actual finite sequence of original entries Q[a+i].
Horner evaluation at one satisfies a guarded QF prefix split and bounded
entry-code congruence. Neither an outer list-code extensionality law nor
an incoming prefix/split identity is assumed. The generic programs are
total; all lists, offsets, lengths and prefix counters are numerical.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSumSegments

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (horner hornerF evaluate qadd qzero canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qadd_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def partialSum (Q r : PTm n) : PTm n := horner Q qone r
def sum (Q : PTm n) : PTm n := evaluate Q qone
def data (Q a : PTm n) : PTm n := pairT Q a
def segmentBody : PTm 2 := entry (fstT (var 1)) (sndT (var 1)+var 0)
def segment (Q a m : PTm n) : PTm n := sequence segmentBody m (data Q a)

@[simp] theorem subst_prefix {l : ℕ} (σ : Fin n → PTm l) (Q r : PTm n) :
    Syn.subst σ (partialSum Q r) = partialSum (Syn.subst σ Q) (Syn.subst σ r) := by simp [partialSum]
@[simp] theorem subst_sum {l : ℕ} (σ : Fin n → PTm l) (Q : PTm n) :
    Syn.subst σ (sum Q) = sum (Syn.subst σ Q) := by simp [sum]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (Q a : PTm n) :
    Syn.subst σ (data Q a) = data (Syn.subst σ Q) (Syn.subst σ a) := by simp [data]
@[simp] theorem subst_segment {l : ℕ} (σ : Fin n → PTm l) (Q a m : PTm n) :
    Syn.subst σ (segment Q a m) = segment (Syn.subst σ Q) (Syn.subst σ a) (Syn.subst σ m) := by simp [segment]

theorem prefix_congr {Q R k l : PTm n} (hQ : Γ ⊢[PRAAx] Q ≐ R) (hk : Γ ⊢[PRAAx] k ≐ l) : Γ ⊢[PRAAx]
    partialSum Q k ≐ partialSum R l := congrAp3 hornerF hk hQ (.eqRefl _)

theorem prefix_zero (Q : PTm n) : Γ ⊢[PRAAx] partialSum Q zero ≐ qzero := GaussianRationalHorner.horner_zero _ _

theorem prefix_canonical (Q r : PTm n) : Γ ⊢[PRAAx] canonical (partialSum Q r) := GaussianRationalHorner.horner_canonical _ _ _

theorem prefix_succ (Q r : PTm n) : Γ ⊢[PRAAx] partialSum Q (succ r) ≐ qadd (partialSum Q r) (entry Q r) :=
  (GaussianRationalHorner.horner_succ Q qone r).eqTrans
    (qadd_congr (GaussianReciprocalHorner.qmul_one_right _ (prefix_canonical Q r)) (.eqRefl _))

theorem segment_body_at (Q a i : PTm n) : Γ ⊢[PRAAx]
    inst2 segmentBody i (data Q a) ≐ entry Q (a+i) := by
  simp only [segmentBody,inst2,Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,
    PTm.subst_add,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact Foundations.SequenceComposition.entry_congr (fst_pair _ _)
    (congrAdd (snd_pair _ _) (.eqRefl _))

theorem segment_length (Q a m : PTm n) : Γ ⊢[PRAAx] length (segment Q a m) ≐ m := sequence_length _ _ _

theorem segment_lookup (Q a m i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    entry (segment Q a m) i ≐ entry Q (a+i) :=
  (sequence_decode segmentBody hi).eqTrans (segment_body_at Q a i)

def entriesEqual (Q R m : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ entry (Syn.shift Q) (var 0) ≐ entry (Syn.shift R) (var 0))

@[simp] theorem subst_entriesEqual {l : ℕ} (σ : Fin n → PTm l) (Q R m : PTm n) :
    (entriesEqual Q R m).subst σ = entriesEqual (Syn.subst σ Q) (Syn.subst σ R) (Syn.subst σ m) := by
  simp [entriesEqual,Syn.subst_shift,Syn.shift_subst]

theorem entry_equal_at (Q R m i : PTm n) (h : Γ ⊢[PRAAx] entriesEqual Q R m)
    (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx] entry Q i ≐ entry R i := by
  have rule : Γ ⊢[PRAAx] lt i m ⟶ entry Q i ≐ entry R i := by simpa [entriesEqual] using h.allE i
  exact .impE rule hi

def congruenceLaw (Q R m r : PTm n) : Fm PTm n := le r m ⟶ partialSum Q r ≐ partialSum R r

@[simp] theorem subst_congruenceLaw {l : ℕ} (σ : Fin n → PTm l) (Q R m r : PTm n) :
    (congruenceLaw Q R m r).subst σ = congruenceLaw (Syn.subst σ Q) (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ r) := by
  simp [congruenceLaw]

/-- Actual prefix equality from bounded individual entry CODE equality;
no equality of the original outer list codes is required. -/
theorem prefix_entries_congr (Q R m r : PTm n) (h : Γ ⊢[PRAAx] entriesEqual Q R m)
    (hr : Γ ⊢[PRAAx] le r m) : Γ ⊢[PRAAx] partialSum Q r ≐ partialSum R r := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] entriesEqual (Syn.shift Q) (Syn.shift R) (Syn.shift m) := by
    simpa only [Fm.shift,subst_entriesEqual,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (congruenceLaw (Syn.shift Q) (Syn.shift R) (Syn.shift m) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_congruenceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((prefix_zero Q).eqTrans (prefix_zero R).eqSymm)
    · simp only [subst_congruenceLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact (prefix_succ (Syn.shift Q) (var 0)).eqTrans
        ((qadd_congr (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
          (entry_equal_at _ _ _ _ hs.wk.wk Prf.hyp0)).eqTrans (prefix_succ (Syn.shift R) (var 0)).eqSymm)
  have rule : Γ ⊢[PRAAx] congruenceLaw Q R m r := by
    simpa only [subst_congruenceLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

def splitLaw (Q a m r : PTm n) : Fm PTm n := le r m ⟶
  partialSum Q (a+r) ≐ qadd (partialSum Q a) (partialSum (segment Q a m) r)

@[simp] theorem subst_splitLaw {l : ℕ} (σ : Fin n → PTm l) (Q a m r : PTm n) :
    (splitLaw Q a m r).subst σ = splitLaw (Syn.subst σ Q) (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ r) := by
  simp [splitLaw]

theorem split_zero (Q a m : PTm n) : Γ ⊢[PRAAx]
    partialSum Q (a+zero) ≐ qadd (partialSum Q a) (partialSum (segment Q a m) zero) :=
  (prefix_congr (.eqRefl _) (add_zero a)).eqTrans
    ((GaussianReciprocalHorner.qadd_zero_right _ (prefix_canonical Q a)).eqSymm.eqTrans
      (qadd_congr (.eqRefl _) (prefix_zero _).eqSymm))

theorem split_step (Q a m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m)
    (ih : Γ ⊢[PRAAx] partialSum Q (a+r) ≐ qadd (partialSum Q a) (partialSum (segment Q a m) r)) : Γ ⊢[PRAAx]
    partialSum Q (a+succ r) ≐ qadd (partialSum Q a) (partialSum (segment Q a m) (succ r)) :=
  (prefix_congr (.eqRefl _) (add_succ a r)).eqTrans
    ((prefix_succ Q (a+r)).eqTrans ((qadd_congr ih (.eqRefl _)).eqTrans
      ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqTrans
        (qadd_congr (.eqRefl _) ((qadd_congr (.eqRefl _) (segment_lookup Q a m r hr).eqSymm).eqTrans
          (prefix_succ (segment Q a m) r).eqSymm)))))

/-- Genuine guarded QF induction on the actual segment prefix. There is
no outer list-length premise, since every original lookup is total. -/
theorem prefix_split (Q a m r : PTm n) (hr : Γ ⊢[PRAAx] le r m) : Γ ⊢[PRAAx]
    partialSum Q (a+r) ≐ qadd (partialSum Q a) (partialSum (segment Q a m) r) := by
  have all : Γ ⊢[PRAAx] .all (splitLaw (Syn.shift Q) (Syn.shift a) (Syn.shift m) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (split_zero Q a m)
    · simp only [subst_splitLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact split_step _ _ _ _ Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] splitLaw Q a m r := by
    simpa only [subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE rule hr

theorem sum_segment (Q a m : PTm n) : Γ ⊢[PRAAx] sum (segment Q a m) ≐ partialSum (segment Q a m) m :=
  prefix_congr (.eqRefl _) (segment_length Q a m)

theorem sum_split (Q a m : PTm n) : Γ ⊢[PRAAx]
    partialSum Q (a+m) ≐ qadd (partialSum Q a) (sum (segment Q a m)) :=
  (prefix_split Q a m m (le_refl _)).eqTrans (qadd_congr (.eqRefl _) (sum_segment Q a m).eqSymm)

theorem prefix_singleton (Q q : PTm n) (hq : Γ ⊢[PRAAx] canonical q)
    (hEntry : Γ ⊢[PRAAx] entry Q zero ≐ q) : Γ ⊢[PRAAx] partialSum Q one ≐ q :=
  (prefix_succ Q zero).eqTrans ((qadd_congr (prefix_zero Q) hEntry).eqTrans
    (GaussianRationalSyntheticDivision.qzero_add q hq))

theorem singleton_sum (Q a q : PTm n) (hq : Γ ⊢[PRAAx] canonical q)
    (hEntry : Γ ⊢[PRAAx] entry Q a ≐ q) : Γ ⊢[PRAAx] sum (segment Q a one) ≐ q :=
  (sum_segment Q a one).eqTrans (prefix_singleton _ q hq
    ((segment_lookup Q a one zero (zero_lt_succ _)).eqTrans
      ((Foundations.SequenceComposition.entry_congr (.eqRefl _) (add_zero a)).eqTrans hEntry)))

def segmentF : PR 3 := PTm.toPR (segment (var 0) (var 1) (var 2))
theorem segment_program (Q a m : PTm n) : Γ ⊢[PRAAx] ap3 segmentF Q a m ≐ segment Q a m := by
  simpa [segmentF,ap3] using toPR_eq (Γ := Γ) (segment (var 0) (var 1) (var 2) : PTm 3) ![Q,a,m]

theorem actual_segment_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 segmentF (var 0) (var 1) (var 2) ≐ segment (var 0) (var 1) (var 2)) ⋏
      length (segment (var 0) (var 1) (var 2)) ≐ var 2) :=
  closeUniv 3 (.andI (segment_program _ _ _) (segment_length _ _ _))

theorem actual_segment_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶ entry (segment (var 0) (var 1) (var 2)) (var 3) ≐ entry (var 0) (var 1+var 3)) :=
  closeUniv 4 (.impI (segment_lookup _ _ _ _ Prf.hyp0))

theorem bounded_prefix_congruence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entriesEqual (var 0) (var 1) (var 2) ⟶ le (var 3) (var 2) ⟶ partialSum (var 0) (var 3) ≐ partialSum (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (prefix_entries_congr _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_prefix_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 2) ⟶ partialSum (var 0) (var 1+var 3) ≐
      qadd (partialSum (var 0) (var 1)) (partialSum (segment (var 0) (var 1) (var 2)) (var 3))) :=
  closeUniv 4 (.impI (prefix_split _ _ _ _ Prf.hyp0))

theorem actual_sum_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (partialSum (var 0) (var 1+var 2) ≐ qadd (partialSum (var 0) (var 1)) (sum (segment (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (sum_split _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalSumSegments
