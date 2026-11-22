import IPRADerivations.Foundations.FiniteFiberGrouping
import IPRADerivations.Core.SumOrder

/-!
# Actual first-cover assignment and the finite covering count

A fixed numerical test reads an original list entry and a candidate
cover index. Bounded cover existence makes the actual first-match
search succeed. The actual filtered index groups preserve original
positions and their order, and their computed sizes sum to the original
list length. The local group-size contract then gives the source ML
bound. No assignment, partition or returned-count law is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteCoverAssignment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open SequenceComposition (length subst_length entry_congr)
open BoundedReflection (wit ex_intro ex_elim ex_least)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def testBody (f : PTm 3) : PTm 2 := inst3 f (var 0) (fstT (var 1)) (sndT (var 1))
def assigned (f : PTm 3) (M v p : PTm n) : PTm n := wit (testBody f) M (pairT v p)
def label (f : PTm 3) (P M p i : PTm n) : PTm n := assigned f M (entry P i) p
def data (P M p : PTm n) : PTm n := pairT P (pairT M p)
def fields (q : PTm n) : Fin 3 → PTm n := ![fstT q,fstT (sndT q),sndT (sndT q)]
def groupData (P M p g : PTm n) : PTm n := pairT (data P M p) g
def groupBody (f : PTm 3) : PTm 2 := eqb
  (label f (fields (fstT (var 1)) 0) (fields (fstT (var 1)) 1) (fields (fstT (var 1)) 2) (var 0))
  (sndT (var 1))
def groupSize (f : PTm 3) (P M p g : PTm n) : PTm n :=
  FilteredEnumerationCode.count (groupBody f) (length P) (groupData P M p g)
def indices (f : PTm 3) (P M p g : PTm n) : PTm n :=
  FilteredEnumerationCode.list (groupBody f) (length P) (groupData P M p g)
def pointBody : PTm 2 := entry (fstT (var 1)) (entry (sndT (var 1)) (var 0))
def group (f : PTm 3) (P M p g : PTm n) : PTm n :=
  sequence pointBody (groupSize f P M p g) (pairT P (indices f P M p g))
def sizeBody (f : PTm 3) : PTm 2 := groupSize f (fields (var 1) 0) (fields (var 1) 1) (fields (var 1) 2) (var 0)
def total (f : PTm 3) (P M p : PTm n) : PTm n := ap2 (sumF (sizeBody f)) M (data P M p)
def incidence (f : PTm 3) (P M p g i : PTm n) : PTm n := Signum.sg (eqb (label f P M p i) g)
def incidenceBody (f : PTm 3) : PTm 3 := incidence f (fields (var 2) 0) (fields (var 2) 1)
  (fields (var 2) 2) (var 0) (var 1)
def hasCover (f : PTm 3) (M v p : PTm n) : Fm PTm n := .ex
  (lt (var 0) (Syn.shift M) ⋏ neg (inst3 f (var 0) (Syn.shift v) (Syn.shift p) ≐ zero))
def cover (f : PTm 3) (P M p : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift P)) ⟶ hasCover f (Syn.shift M) (entry (Syn.shift P) (var 0)) (Syn.shift p))
def groupBounds (f : PTm 3) (P M p L : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift M) ⟶ le (groupSize f (Syn.shift P) (Syn.shift M) (Syn.shift p) (var 0)) (Syn.shift L))

@[simp] theorem subst_assigned {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (M v p : PTm n) :
    Syn.subst σ (assigned f M v p) = assigned f (Syn.subst σ M) (Syn.subst σ v) (Syn.subst σ p) := by simp [assigned,wit,Search.mu]
@[simp] theorem subst_label {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p i : PTm n) :
    Syn.subst σ (label f P M p i) = label f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) (Syn.subst σ i) := by simp [label]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (P M p : PTm n) :
    Syn.subst σ (data P M p) = data (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) := by simp [data]
@[simp] theorem subst_fields {k : ℕ} (σ : Fin n → PTm k) (q : PTm n) (i : Fin 3) :
    Syn.subst σ (fields q i) = fields (Syn.subst σ q) i := by fin_cases i <;> simp [fields]
@[simp] theorem subst_groupData {k : ℕ} (σ : Fin n → PTm k) (P M p g : PTm n) :
    Syn.subst σ (groupData P M p g) = groupData (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) (Syn.subst σ g) := by simp [groupData]
@[simp] theorem subst_groupSize {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p g : PTm n) :
    Syn.subst σ (groupSize f P M p g) = groupSize f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) (Syn.subst σ g) := by simp [groupSize]
@[simp] theorem subst_indices {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p g : PTm n) :
    Syn.subst σ (indices f P M p g) = indices f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) (Syn.subst σ g) := by simp [indices]
@[simp] theorem subst_group {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p g : PTm n) :
    Syn.subst σ (group f P M p g) = group f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) (Syn.subst σ g) := by simp [group]
@[simp] theorem subst_total {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p : PTm n) :
    Syn.subst σ (total f P M p) = total f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) := by simp [total]
@[simp] theorem subst_incidence {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p g i : PTm n) :
    Syn.subst σ (incidence f P M p g i) = incidence f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) (Syn.subst σ g) (Syn.subst σ i) := by simp [incidence,Signum.sg]
@[simp] theorem subst_hasCover {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (M v p : PTm n) :
    (hasCover f M v p).subst σ = hasCover f (Syn.subst σ M) (Syn.subst σ v) (Syn.subst σ p) := by
  simp [hasCover,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_cover {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p : PTm n) :
    (cover f P M p).subst σ = cover f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) := by
  simp [cover,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_groupBounds {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p L : PTm n) :
    (groupBounds f P M p L).subst σ = groupBounds f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) (Syn.subst σ L) := by
  simp [groupBounds,Syn.subst_shift,Syn.shift_subst]

theorem fields_at (P M p : PTm n) (j : Fin 3) : Γ ⊢[PRAAx] fields (data P M p) j ≐ ![P,M,p] j := by
  fin_cases j
  · exact fst_pair _ _
  · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
theorem label_congr (f : PTm 3) {P P' M M' p p' i i' : PTm n} (hP : Γ ⊢[PRAAx] P ≐ P')
    (hM : Γ ⊢[PRAAx] M ≐ M') (hp : Γ ⊢[PRAAx] p ≐ p') (hi : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] label f P M p i ≐ label f P' M' p' i' := by
  simpa only [subst_label,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ)
      (label f (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![P,M,p,i]) (σ' := ![P',M',p',i'])
        (fun j => by fin_cases j; exact hP; exact hM; exact hp; exact hi)
theorem test_body_at (f : PTm 3) (g v p : PTm n) : Γ ⊢[PRAAx]
    inst2 (testBody f) g (pairT v p) ≐ inst3 f g v p := by
  simp only [testBody,subst_inst3,inst2,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrInst3 f (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

theorem assigned_bound (f : PTm 3) (M v p : PTm n) : Γ ⊢[PRAAx] le (assigned f M v p) M :=
  .andE₁ (Search.search_spec (f := BoundedReflection.nB (testBody f)) M zero (pairT v p))
theorem assigned_found (f : PTm 3) (M v p g : PTm n) (hg : Γ ⊢[PRAAx] lt g M)
    (h : Γ ⊢[PRAAx] neg (inst3 f g v p ≐ zero)) : Γ ⊢[PRAAx]
    lt (assigned f M v p) M ⋏ neg (inst3 f (assigned f M v p) v p ≐ zero) := by
  have ne : Γ ⊢[PRAAx] neg (inst2 (testBody f) g (pairT v p) ≐ zero) :=
    .impI (.impE h.wk ((test_body_at f g v p).wk.eqSymm.eqTrans Prf.hyp0))
  have hit := ex_elim (testBody f) (ex_intro (testBody f) ne hg)
  exact .andI (.andE₁ hit) (.impI (.impE (Prf.andE₂ hit).wk ((test_body_at f _ v p).wk.eqTrans Prf.hyp0)))

theorem cover_label (f : PTm 3) (P M p i : PTm n) (h : Γ ⊢[PRAAx] cover f P M p)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    lt (label f P M p i) M ⋏ neg (inst3 f (label f P M p i) (entry P i) p ≐ zero) := by
  have rule : Γ ⊢[PRAAx] lt i (length P) ⟶ hasCover f M (entry P i) p := by
    simpa [cover] using h.allE i
  refine .exE (.impE rule hi) ?_
  simpa only [Fm.shift,Fm.subst_and,subst_lt,subst_neg,Fm.subst_eq,subst_label,subst_inst3,
    subst_entry,Syn.shift,label,subst_assigned,ConciseIPRA.PTm.subst_zero] using
    assigned_found f (Syn.shift M) (entry (Syn.shift P) (Syn.shift i)) (Syn.shift p) (var 0)
      (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)

theorem group_fields_at (P M p g : PTm n) (j : Fin 3) : Γ ⊢[PRAAx]
    fields (fstT (groupData P M p g)) j ≐ ![P,M,p] j := by
  fin_cases j
  · exact (congrFst (fst_pair _ _)).eqTrans (fields_at _ _ _ 0)
  · exact (congrFst (congrSnd (fst_pair _ _))).eqTrans (fields_at _ _ _ 1)
  · exact (congrSnd (congrSnd (fst_pair _ _))).eqTrans (fields_at _ _ _ 2)
theorem group_body_at (f : PTm 3) (P M p g i : PTm n) : Γ ⊢[PRAAx]
    inst2 (groupBody f) i (groupData P M p g) ≐ eqb (label f P M p i) g := by
  simp only [groupBody,inst2,subst_eqb,subst_label,subst_fields,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact FiniteFiberGrouping.eqb_congr
    (label_congr f (group_fields_at P M p g 0) (group_fields_at P M p g 1) (group_fields_at P M p g 2) (.eqRefl _))
    (snd_pair _ _)
theorem indices_length (f : PTm 3) (P M p g : PTm n) : Γ ⊢[PRAAx]
    length (indices f P M p g) ≐ groupSize f P M p g := FilteredEnumerationCode.list_length _ _ _
theorem group_length (f : PTm 3) (P M p g : PTm n) : Γ ⊢[PRAAx]
    length (group f P M p g) ≐ groupSize f P M p g := sequence_length _ _ _
theorem index_bound (f : PTm 3) (P M p g r : PTm n) (hr : Γ ⊢[PRAAx] lt r (groupSize f P M p g)) : Γ ⊢[PRAAx]
    lt (entry (indices f P M p g) r) (length P) := FilteredEnumerationCode.entry_bound _ _ _ _ hr
theorem index_label (f : PTm 3) (P M p g r : PTm n) (hr : Γ ⊢[PRAAx] lt r (groupSize f P M p g)) : Γ ⊢[PRAAx]
    label f P M p (entry (indices f P M p g) r) ≐ g :=
  FiniteFiberGrouping.equality_of_nonzero_eqb
    (.impI (.impE (FilteredEnumerationCode.entry_valid (groupBody f) (length P) (groupData P M p g) r hr).wk
      ((group_body_at f P M p g _).wk.eqTrans Prf.hyp0)))
theorem indices_increasing (f : PTm 3) (P M p g r s : PTm n) (hrs : Γ ⊢[PRAAx] lt r s)
    (hs : Γ ⊢[PRAAx] lt s (groupSize f P M p g)) : Γ ⊢[PRAAx]
    lt (entry (indices f P M p g) r) (entry (indices f P M p g) s) :=
  FilteredEnumerationCode.increasing _ _ _ _ _ hrs hs
theorem point_body_at (P I r : PTm n) : Γ ⊢[PRAAx]
    inst2 pointBody r (pairT P I) ≐ entry P (entry I r) := by
  simp only [pointBody,inst2,subst_entry,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact entry_congr (fst_pair _ _) (entry_congr (snd_pair _ _) (.eqRefl _))
theorem group_lookup (f : PTm 3) (P M p g r : PTm n) (hr : Γ ⊢[PRAAx] lt r (groupSize f P M p g)) : Γ ⊢[PRAAx]
    entry (group f P M p g) r ≐ entry P (entry (indices f P M p g) r) :=
  (sequence_decode pointBody (x := pairT P (indices f P M p g)) hr).eqTrans (point_body_at _ _ _)

def slot (f : PTm 3) (P M p g i : PTm n) : PTm n :=
  FilteredEnumeration.rank (groupBody f) i (groupData P M p g)
@[simp] theorem subst_slot {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p g i : PTm n) :
    Syn.subst σ (slot f P M p g i) = slot f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) (Syn.subst σ g) (Syn.subst σ i) := by
  simp [slot,FilteredEnumeration.rank]
theorem group_complete (f : PTm 3) (P M p g i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hg : Γ ⊢[PRAAx] label f P M p i ≐ g) : Γ ⊢[PRAAx]
    lt (slot f P M p g i) (groupSize f P M p g) ⋏
      (entry (indices f P M p g) (slot f P M p g i) ≐ i) :=
  FilteredEnumerationCode.listed (groupBody f) (length P) (groupData P M p g) i hi
    (.impI (succ_ne_zero (((group_body_at f P M p g i).eqTrans (eqb_of_eq hg)).wk.eqSymm.eqTrans Prf.hyp0)))
theorem coverage (f : PTm 3) (P M p i : PTm n) (h : Γ ⊢[PRAAx] cover f P M p)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    lt (label f P M p i) M ⋏
      (lt (slot f P M p (label f P M p i) i) (groupSize f P M p (label f P M p i)) ⋏
        (entry (group f P M p (label f P M p i)) (slot f P M p (label f P M p i) i) ≐ entry P i)) := by
  have hit := group_complete f P M p (label f P M p i) i hi (.eqRefl _)
  exact .andI (.andE₁ (cover_label f P M p i h hi)) (.andI (.andE₁ hit)
    ((group_lookup f P M p _ _ (.andE₁ hit)).eqTrans (entry_congr (.eqRefl _) (.andE₂ hit))))

theorem size_at (f : PTm 3) (P M p g : PTm n) : Γ ⊢[PRAAx]
    inst2 (sizeBody f) g (data P M p) ≐ groupSize f P M p g := by
  simp only [sizeBody,inst2,subst_groupSize,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [subst_groupSize,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (groupSize f (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fields (data P M p) 0,fields (data P M p) 1,fields (data P M p) 2,g]) (σ' := ![P,M,p,g])
      (fun j => by fin_cases j; exact fields_at _ _ _ 0; exact fields_at _ _ _ 1; exact fields_at _ _ _ 2; exact .eqRefl _)

theorem incidence_at (f : PTm 3) (P M p g i : PTm n) : Γ ⊢[PRAAx]
    inst3 (incidenceBody f) g i (data P M p) ≐ incidence f P M p g i := by
  have last1 : ![fields (data P M p) 0,fields (data P M p) 1,fields (data P M p) 2,g,i] (4 : Fin 5) = i := rfl
  simp only [incidenceBody,subst_incidence,inst3,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  simpa only [subst_incidence,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,last1,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (incidence f (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![fields (data P M p) 0,fields (data P M p) 1,fields (data P M p) 2,g,i]) (σ' := ![P,M,p,g,i])
      (fun j => by
        fin_cases j
        · exact fields_at _ _ _ 0
        · exact fields_at _ _ _ 1
        · exact fields_at _ _ _ 2
        · exact .eqRefl _
        · exact .eqRefl _)
theorem row_at (f : PTm 3) (P M p g i : PTm n) : Γ ⊢[PRAAx]
    inst2 (rowB (incidenceBody f)) i (pairT g (data P M p)) ≐ incidence f P M p g i := by
  rw [inst2_rowB]
  exact (congrInst3 (incidenceBody f) (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans (incidence_at f P M p g i)
theorem column_at (f : PTm 3) (P M p g i : PTm n) : Γ ⊢[PRAAx]
    inst2 (colB (incidenceBody f)) g (pairT i (data P M p)) ≐ incidence f P M p g i := by
  rw [inst2_colB]
  exact (congrInst3 (incidenceBody f) (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans (incidence_at f P M p g i)
theorem row_count (f : PTm 3) (P M p g : PTm n) : Γ ⊢[PRAAx]
    groupSize f P M p g ≐ ap2 (sumF (rowB (incidenceBody f))) (length P) (pairT g (data P M p)) := by
  apply sum_congr_bounded
  refine .allI (.impI ?_)
  rw [BoundedReflection.inst2_sgB]
  have eq := congrMonus (Γ := lt (var 0) (Syn.shift (length P)) :: Γ.map Fm.shift) (.eqRefl one)
    (congrMonus (.eqRefl one) (group_body_at f (Syn.shift P) (Syn.shift M) (Syn.shift p) (Syn.shift g) (var 0)))
  simpa only [Syn.shift,subst_groupData,subst_data,subst_pairT] using eq.eqTrans
    (row_at f (Syn.shift P) (Syn.shift M) (Syn.shift p) (Syn.shift g) (var 0)).eqSymm

theorem column_unit (f : PTm 3) (P M p i : PTm n) (h : Γ ⊢[PRAAx] cover f P M p)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    ap2 (sumF (colB (incidenceBody f))) M (pairT i (data P M p)) ≐ one := by
  have eq : Γ ⊢[PRAAx] ap2 (sumF (colB (incidenceBody f))) M (pairT i (data P M p)) ≐
      dS (one : PTm 2) M (label f P M p i) zero := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    rw [inst2_dB]
    let Δ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
    have l := (column_at (Γ := Δ) f (Syn.shift P) (Syn.shift M) (Syn.shift p) (var 0) (Syn.shift i)).eqTrans
      (FiniteFiberGrouping.sg_eqb (label f (Syn.shift P) (Syn.shift M) (Syn.shift p) (Syn.shift i)) (var 0))
    have r := (congrMul (Γ := Δ)
      (FiniteFiberGrouping.eqb_congr (fst_pair (label f (Syn.shift P) (Syn.shift M) (Syn.shift p) (Syn.shift i)) zero) (.eqRefl (var 0)))
      (.eqRefl one)).eqTrans ((mul_comm _ one).eqTrans (one_mul _))
    simpa only [Δ,Syn.shift,subst_pairT,subst_data,subst_label,inst2,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using l.eqTrans r.eqSymm
  have delta := sum_delta (Γ := Γ) (one : PTm 2) (x := zero) (.andE₁ (cover_label f P M p i h hi))
  exact eq.eqTrans (by simpa only [inst2,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using delta)

theorem cardinal_partition (f : PTm 3) (P M p : PTm n) (h : Γ ⊢[PRAAx] cover f P M p) : Γ ⊢[PRAAx]
    total f P M p ≐ length P := by
  have rows : Γ ⊢[PRAAx] total f P M p ≐ ap2 (sumF (oB (incidenceBody f))) M (pairT (length P) (data P M p)) := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    have e := (size_at (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift)
      f (Syn.shift P) (Syn.shift M) (Syn.shift p) (var 0)).eqTrans
        ((row_count f (Syn.shift P) (Syn.shift M) (Syn.shift p) (var 0)).eqTrans
          (oB_at (incidenceBody f) (var 0) (length (Syn.shift P)) (data (Syn.shift P) (Syn.shift M) (Syn.shift p))).eqSymm)
    simpa only [Syn.shift,subst_pairT,subst_length,subst_data] using e
  have hs : Γ.map Fm.shift ⊢[PRAAx] cover f (Syn.shift P) (Syn.shift M) (Syn.shift p) := by
    simpa only [Fm.shift,subst_cover,Syn.shift] using h.shift
  have columns : Γ ⊢[PRAAx] ap2 (sumF (pB (incidenceBody f))) (length P) (pairT M (data P M p)) ≐
      ap2 (sumF (one : PTm 2)) (length P) zero := by
    apply sum_congr_bounded
    refine .allI (.impI ?_)
    rw [inst2_pB]
    let Δ := lt (var 0) (Syn.shift (length P)) :: Γ.map Fm.shift
    have point := column_unit (Γ := Δ) f (Syn.shift P) (Syn.shift M) (Syn.shift p) (var 0) hs.wk
      (by simpa only [Δ,Syn.shift,subst_length] using (Prf.hyp0 : Δ ⊢[PRAAx] _))
    have decode := congrAp2 (Γ := Δ) (sumF (colB (incidenceBody f)))
      (fst_pair (Syn.shift M) (data (Syn.shift P) (Syn.shift M) (Syn.shift p)))
      (congrPairT (.eqRefl (var 0)) (snd_pair (Syn.shift M) (data (Syn.shift P) (Syn.shift M) (Syn.shift p))))
    simpa only [Δ,Syn.shift,subst_pairT,subst_data,inst2,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using decode.eqTrans point
  exact rows.eqTrans ((fubini (incidenceBody f) M (length P) (data P M p)).eqTrans
    (columns.eqTrans (FiniteFiberGrouping.sum_units (length P) zero)))

theorem assigned_before (f : PTm 3) (M v p g : PTm n) (hg : Γ ⊢[PRAAx] lt g (assigned f M v p)) : Γ ⊢[PRAAx]
    inst3 f g v p ≐ zero := (test_body_at f g v p).eqSymm.eqTrans (ex_least (testBody f) hg)
theorem assigned_least (f : PTm 3) (M v p g : PTm n) (h : Γ ⊢[PRAAx] neg (inst3 f g v p ≐ zero)) : Γ ⊢[PRAAx]
    le (assigned f M v p) g := by
  refine .orE (lt_or_le g (assigned f M v p)) ?_ Prf.hyp0
  exact .botE _ (.impE h.wk (assigned_before f M v p g Prf.hyp0))

theorem group_test (f : PTm 3) (P M p g r : PTm n) (h : Γ ⊢[PRAAx] cover f P M p)
    (hr : Γ ⊢[PRAAx] lt r (groupSize f P M p g)) : Γ ⊢[PRAAx]
    neg (inst3 f g (entry (group f P M p g) r) p ≐ zero) := by
  have old := Prf.andE₂ (cover_label f P M p (entry (indices f P M p g) r) h (index_bound f P M p g r hr))
  have eq := congrInst3 f (index_label f P M p g r hr) (group_lookup f P M p g r hr).eqSymm (.eqRefl p)
  exact .impI (.impE old.wk (eq.wk.eqTrans Prf.hyp0))

theorem property_inst (φ : Fm PTm 2) (P q i : PTm n) :
    (φ.subst ![entry (Syn.shift P) (var 0),Syn.shift q]).subst (Syn.inst i) = φ.subst ![entry P i,q] := by
  rw [Fm.subst_subst]
  congr 1
  funext j
  fin_cases j <;> simp
theorem property_congr (φ : Fm PTm 2) (a b q : PTm n) (e : Γ ⊢[PRAAx] a ≐ b)
    (h : Γ ⊢[PRAAx] φ.subst ![a,q]) : Γ ⊢[PRAAx] φ.subst ![b,q] :=
  Prf.eqSubst φ ![a,q] ![b,q] (fun j => by fin_cases j; exact e; exact .eqRefl _) h

/-- Any original entry property, with arbitrary logical complexity, is
inherited using the actual retained original index and code equality. -/
theorem group_property_at (φ : Fm PTm 2) (f : PTm 3) (P M p g r q : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (length (Syn.shift P)) ⟶
      φ.subst ![entry (Syn.shift P) (var 0),Syn.shift q]))
    (hr : Γ ⊢[PRAAx] lt r (groupSize f P M p g)) : Γ ⊢[PRAAx]
    φ.subst ![entry (group f P M p g) r,q] := by
  have rule : Γ ⊢[PRAAx] lt (entry (indices f P M p g) r) (length P) ⟶
      φ.subst ![entry P (entry (indices f P M p g) r),q] := by
    simpa only [Fm.subst_imp,property_inst,subst_lt,subst_length,Syn.subst_var,Syn.inst_zero,
      Syn.subst_inst_shift] using h.allE (entry (indices f P M p g) r)
  exact property_congr φ _ _ q (group_lookup f P M p g r hr).eqSymm
    (.impE rule (index_bound f P M p g r hr))

theorem constant_sum (N L : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (var 1 : PTm 2)) N L ≐ N*L := by
  have all : Γ ⊢[PRAAx] .all (ap2 (sumF (var 1 : PTm 2)) (var 0) (Syn.shift L) ≐ var 0*Syn.shift L) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,subst_ap2,PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (sum_zero _ _).eqTrans (zero_mul _).eqSymm
    · simp only [Fm.subst_eq,subst_ap2,PTm.subst_mul,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      have e := sum_succ' (Γ := (ap2 (sumF (var 1 : PTm 2)) (var 0) (Syn.shift L) ≐ var 0*Syn.shift L) :: Γ.map Fm.shift)
        (var 1 : PTm 2) (var 0) (Syn.shift L)
      exact e.eqTrans ((congrAdd Prf.hyp0 (by simp [inst2]; exact .eqRefl _)).eqTrans (succ_mul _ _).eqSymm)
  simpa only [Fm.subst_eq,subst_ap2,PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem total_bound (f : PTm 3) (P M p L : PTm n) (h : Γ ⊢[PRAAx] groupBounds f P M p L) : Γ ⊢[PRAAx]
    le (total f P M p) (M*L) := by
  have sums : Γ ⊢[PRAAx] le (total f P M p) (ap2 (sumF (var 1 : PTm 2)) M L) := by
    refine sum_le_params (sizeBody f) (var 1 : PTm 2) (data P M p) L M (.allI (.impI ?_))
    have b := Prf.impE h.allOpen.wk (Prf.hyp0 : lt (var 0) (Syn.shift M) :: Γ.map Fm.shift ⊢[PRAAx] _)
    simpa only [Syn.shift,subst_data,inst2,Syn.subst_var,Matrix.cons_val_one,Matrix.cons_val_zero] using
      le_congr (size_at f (Syn.shift P) (Syn.shift M) (Syn.shift p) (var 0)).eqSymm (.eqRefl (Syn.shift L)) b
  exact le_congr (.eqRefl _) (constant_sum M L) sums
theorem cover_count (f : PTm 3) (P M p L : PTm n) (h : Γ ⊢[PRAAx] cover f P M p)
    (hSizes : Γ ⊢[PRAAx] groupBounds f P M p L) : Γ ⊢[PRAAx] le (length P) (M*L) :=
  le_congr (cardinal_partition f P M p h) (.eqRefl _) (total_bound f P M p L hSizes)

theorem empty_cover (f : PTm 3) (P p : PTm n) (h : Γ ⊢[PRAAx] cover f P zero p) : Γ ⊢[PRAAx] length P ≐ zero :=
  (cardinal_partition f P zero p h).eqSymm.eqTrans (sum_zero _ _)

def groupListBody (f : PTm 3) : PTm 2 := group f (fields (var 1) 0) (fields (var 1) 1) (fields (var 1) 2) (var 0)
def groups (f : PTm 3) (P M p : PTm n) : PTm n := sequence (groupListBody f) M (data P M p)
def sizes (f : PTm 3) (P M p : PTm n) : PTm n := sequence (sizeBody f) M (data P M p)
def output (f : PTm 3) (P M p : PTm n) : PTm n := pairT (groups f P M p) (pairT (sizes f P M p) (total f P M p))
def outputF (f : PTm 3) : PR 3 := PTm.toPR (output f (var 0) (var 1) (var 2))
def run (f : PTm 3) (P M p : PTm n) : PTm n := app (outputF f) ![P,M,p]

@[simp] theorem subst_groups {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p : PTm n) :
    Syn.subst σ (groups f P M p) = groups f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) := by simp [groups]
@[simp] theorem subst_sizes {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p : PTm n) :
    Syn.subst σ (sizes f P M p) = sizes f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) := by simp [sizes]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p : PTm n) :
    Syn.subst σ (output f P M p) = output f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (f : PTm 3) (P M p : PTm n) :
    Syn.subst σ (run f P M p) = run f (Syn.subst σ P) (Syn.subst σ M) (Syn.subst σ p) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl
theorem groups_length (f : PTm 3) (P M p : PTm n) : Γ ⊢[PRAAx] length (groups f P M p) ≐ M := sequence_length _ _ _
theorem sizes_length (f : PTm 3) (P M p : PTm n) : Γ ⊢[PRAAx] length (sizes f P M p) ≐ M := sequence_length _ _ _
theorem group_list_body_at (f : PTm 3) (P M p g : PTm n) : Γ ⊢[PRAAx]
    inst2 (groupListBody f) g (data P M p) ≐ group f P M p g := by
  simp only [groupListBody,inst2,subst_group,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa only [subst_group,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (group f (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fields (data P M p) 0,fields (data P M p) 1,fields (data P M p) 2,g]) (σ' := ![P,M,p,g])
      (fun j => by fin_cases j; exact fields_at _ _ _ 0; exact fields_at _ _ _ 1; exact fields_at _ _ _ 2; exact .eqRefl _)
theorem groups_lookup (f : PTm 3) (P M p g : PTm n) (hg : Γ ⊢[PRAAx] lt g M) : Γ ⊢[PRAAx]
    entry (groups f P M p) g ≐ group f P M p g :=
  (sequence_decode (groupListBody f) (x := data P M p) hg).eqTrans (group_list_body_at f P M p g)
theorem sizes_lookup (f : PTm 3) (P M p g : PTm n) (hg : Γ ⊢[PRAAx] lt g M) : Γ ⊢[PRAAx]
    entry (sizes f P M p) g ≐ groupSize f P M p g :=
  (sequence_decode (sizeBody f) (x := data P M p) hg).eqTrans (size_at f P M p g)
theorem program_at (f : PTm 3) (P M p : PTm n) : Γ ⊢[PRAAx] run f P M p ≐ output f P M p := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output f (var 0) (var 1) (var 2) : PTm 3) ![P,M,p]
theorem returned_groups (f : PTm 3) (P M p : PTm n) : Γ ⊢[PRAAx] fstT (run f P M p) ≐ groups f P M p :=
  (congrFst (program_at f P M p)).eqTrans (fst_pair _ _)
theorem returned_sizes (f : PTm 3) (P M p : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run f P M p)) ≐ sizes f P M p :=
  (congrFst ((congrSnd (program_at f P M p)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_total (f : PTm 3) (P M p : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run f P M p)) ≐ total f P M p :=
  (congrSnd ((congrSnd (program_at f P M p)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_partition (f : PTm 3) (P M p : PTm n) (h : Γ ⊢[PRAAx] cover f P M p) : Γ ⊢[PRAAx]
    sndT (sndT (run f P M p)) ≐ length P := (returned_total f P M p).eqTrans (cardinal_partition f P M p h)

theorem actual_first_cover_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (cover f (var 0) (var 1) (var 2) ⟶ lt (var 3) (length (var 0)) ⟶
      lt (label f (var 0) (var 1) (var 2) (var 3)) (var 1) ⋏
        neg (inst3 f (label f (var 0) (var 1) (var 2) (var 3)) (entry (var 0) (var 3)) (var 2) ≐ zero)) :=
  closeUniv 4 (.impI (.impI (cover_label f _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_least_cover_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (neg (inst3 f (var 3) (var 1) (var 2) ≐ zero) ⟶ le (assigned f (var 0) (var 1) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (assigned_least f _ _ _ _ Prf.hyp0))
theorem actual_group_lookup_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (groupSize f (var 0) (var 1) (var 2) (var 3)) ⟶
      entry (group f (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        entry (var 0) (entry (indices f (var 0) (var 1) (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (group_lookup f _ _ _ _ _ Prf.hyp0))
theorem actual_group_index_bound_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (groupSize f (var 0) (var 1) (var 2) (var 3)) ⟶
      lt (entry (indices f (var 0) (var 1) (var 2) (var 3)) (var 4)) (length (var 0))) :=
  closeUniv 5 (.impI (index_bound f _ _ _ _ _ Prf.hyp0))
theorem actual_group_order_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 4) (var 5) ⟶ lt (var 5) (groupSize f (var 0) (var 1) (var 2) (var 3)) ⟶
      lt (entry (indices f (var 0) (var 1) (var 2) (var 3)) (var 4))
        (entry (indices f (var 0) (var 1) (var 2) (var 3)) (var 5))) :=
  closeUniv 6 (.impI (.impI (indices_increasing f _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_group_test_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (cover f (var 0) (var 1) (var 2) ⟶ lt (var 4) (groupSize f (var 0) (var 1) (var 2) (var 3)) ⟶
      neg (inst3 f (var 3) (entry (group f (var 0) (var 1) (var 2) (var 3)) (var 4)) (var 2) ≐ zero)) :=
  closeUniv 5 (.impI (.impI (group_test f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cardinal_partition_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (cover f (var 0) (var 1) (var 2) ⟶ total f (var 0) (var 1) (var 2) ≐ length (var 0)) :=
  closeUniv 3 (.impI (cardinal_partition f _ _ _ Prf.hyp0))
theorem actual_cover_count_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (cover f (var 0) (var 1) (var 2) ⟶ groupBounds f (var 0) (var 1) (var 2) (var 3) ⟶
      le (length (var 0)) (var 1*var 3)) :=
  closeUniv 4 (.impI (.impI (cover_count f _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_empty_cover_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (cover f (var 0) zero (var 1) ⟶ length (var 0) ≐ zero) := closeUniv 2 (.impI (empty_cover f _ _ Prf.hyp0))
theorem actual_program_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run f (var 0) (var 1) (var 2) ≐ output f (var 0) (var 1) (var 2)) := closeUniv 3 (program_at f _ _ _)
theorem actual_returned_partition_closed (f : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (cover f (var 0) (var 1) (var 2) ⟶ sndT (sndT (run f (var 0) (var 1) (var 2))) ≐ length (var 0)) :=
  closeUniv 3 (.impI (returned_partition f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Foundations.FiniteCoverAssignment
