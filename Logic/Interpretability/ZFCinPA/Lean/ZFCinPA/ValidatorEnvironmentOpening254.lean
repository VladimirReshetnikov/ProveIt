import ZFCinPA.ValidatorEnvironmentLabels254
import ZFCinPA.ValidatorEnvironmentSubstitution254
import ZFCinPA.ModelCodedSpecialization

set_option autoImplicit false
noncomputable section

/-!
Source opening in a configurable internal environment. The distinguished
bound slot can be any internal index d: lower slots retain their labels,
and the final slot is moved to the head of the free environment. All state
and syntax values are internal. This is a syntax identity, without a CProv
proof-renaming, freshness or alpha-conversion assertion.
-/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open ValidatorEnvironmentLabels254 ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- B' extends B at its final slot; all dimensions and indices are internal. -/
def Ext (d B B' x : V) : Prop :=
  len B=d ∧ len B'=d+1 ∧ (∀ i<d, B'.[i]=B.[i]) ∧ B'.[d]=x

lemma ext_zero (x : V) : Ext (0 : V) 0 (x∷0) x := by simp [Ext]
lemma ext_cons {d B B' x : V} (h : Ext d B B' x) (label : V) :
    Ext (d+1) (label∷B) (label∷B') x := by
  refine ⟨by simpa using congrArg (fun z : V => z+1) h.1,
    by simpa using congrArg (fun z : V => z+1) h.2.1,?_,?_⟩
  · intro i hi
    rcases zero_or_succ i with (rfl | ⟨i,rfl⟩)
    · simp
    · simpa using h.2.2.1 i (by simpa using hi)
  · simpa using h.2.2.2

noncomputable def openingVec (d : V) : V := qVecIter ℒₛₑₜ d (^&0∷0)
lemma openingVec_typed (d : V) : IsSemitermVec ℒₛₑₜ (d+1) d (openingVec d) := by
  simpa [openingVec,add_comm] using qVecIter_isSemitermVec (L := ℒₛₑₜ)
    (show IsSemitermVec (V := V) ℒₛₑₜ 1 0 (^&0∷0) by simp) d
@[simp] lemma openingVec_succ (d : V) : openingVec (d+1)=qVec ℒₛₑₜ (openingVec d) :=
  qVecIter_succ d _

noncomputable def termOpenAt (d source : V) : V :=
  termSubst ℒₛₑₜ (openingVec d) (termShift ℒₛₑₜ source)
noncomputable def openAt (d source : V) : V :=
  subst ℒₛₑₜ (openingVec d) (shift ℒₛₑₜ source)

private lemma opening_matches (d F B B' x : V) (hB : Ext d B B' x) :
    ValidatorEnvironmentSubstitution254.Matches (x∷F) B B' (d+1) (openingVec d) := by
  intro i hi
  by_cases hid : i<d
  · rw [show (openingVec d).[i]=(^#i : V) from
      (qVecIter_free_spec (L := ℒₛₑₜ) d 0).1 i hid]
    rw [TermLabels.term_bvar,hB.2.2.1 i hid]
  · have he : i=d := le_antisymm (lt_succ_iff_le.mp hi) (le_of_not_gt hid)
    subst i
    rw [show (openingVec d).[d]=(^&0 : V) from
      (qVecIter_free_spec (L := ℒₛₑₜ) d 0).2]
    rw [TermLabels.term_fvar,freeLabel_cons_zero,hB.2.2.2]

lemma term_labels_open {d source : V} (ht : IsSemiterm ℒₛₑₜ (d+1) source)
    (F B B' x : V) (hB : Ext d B B' x) :
    TermLabels.term (x∷F) B (termOpenAt d source)=TermLabels.term F B' source := by
  have h := ValidatorEnvironmentSubstitution254.term_labels_subst ht.termShift
    (opening_matches d F B B' x hB)
  simpa only [termOpenAt,TermLabels.term_shift ht.isUTerm,tail_cons] using h

lemma vec_labels_open {d arity terms : V} (ht : IsSemitermVec ℒₛₑₜ arity (d+1) terms)
    (F B B' x : V) (hB : Ext d B B' x) :
    TermLabels.vec (x∷F) B arity
      (termSubstVec ℒₛₑₜ arity (openingVec d) (termShiftVec ℒₛₑₜ arity terms))=
      TermLabels.vec F B' arity terms := by
  have h := ValidatorEnvironmentSubstitution254.vec_labels_subst ht.termShiftVec
    (openingVec_typed d) (opening_matches d F B B' x hB)
  simpa only [TermLabels.vec_shift (x∷F) B' ht.isUTerm,tail_cons] using h

lemma openAt_isSemiformula {d p : V} (hp : IsSemiformula ℒₛₑₜ (d+1) p) :
    IsSemiformula ℒₛₑₜ d (openAt d p) := hp.shift.subst (openingVec_typed d)

lemma openAt_rel (d : V) {arity R terms : V}
    (hr : (ℒₛₑₜ).IsRel arity R) (ht : IsUTermVec ℒₛₑₜ arity terms) :
    openAt d (^rel arity R terms)=
      ^rel arity R (termSubstVec ℒₛₑₜ arity (openingVec d) (termShiftVec ℒₛₑₜ arity terms)) := by
  rw [openAt,shift_rel hr ht,substs_rel hr ht.termShiftVec]
lemma openAt_nrel (d : V) {arity R terms : V}
    (hr : (ℒₛₑₜ).IsRel arity R) (ht : IsUTermVec ℒₛₑₜ arity terms) :
    openAt d (^nrel arity R terms)=
      ^nrel arity R (termSubstVec ℒₛₑₜ arity (openingVec d) (termShiftVec ℒₛₑₜ arity terms)) := by
  rw [openAt,shift_nrel hr ht,substs_nrel hr ht.termShiftVec]
@[simp] lemma openAt_verum (d : V) : openAt d (^⊤ : V)=^⊤ := by simp [openAt]
@[simp] lemma openAt_falsum (d : V) : openAt d (^⊥ : V)=^⊥ := by simp [openAt]
lemma openAt_and (d : V) {p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    openAt d (p ^⋏ q)=openAt d p ^⋏ openAt d q := by
  rw [openAt,shift_and hp hq,substs_and hp.shift hq.shift];rfl
lemma openAt_or (d : V) {p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    openAt d (p ^⋎ q)=openAt d p ^⋎ openAt d q := by
  rw [openAt,shift_or hp hq,substs_or hp.shift hq.shift];rfl
lemma openAt_all (d : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    openAt d (^∀ p)=^∀ (openAt (d+1) p) := by
  rw [openAt,shift_all hp,substs_all hp.shift,←openingVec_succ];rfl
lemma openAt_exs (d : V) {p : V} (hp : IsUFormula ℒₛₑₜ p) :
    openAt d (^∃ p)=^∃ (openAt (d+1) p) := by
  rw [openAt,shift_exs hp,substs_ex hp.shift,←openingVec_succ];rfl

private instance qVecIter_delta : 𝚫₁-Function₂[V] (qVecIter ℒₛₑₜ) :=
  qVecIter_defined.graph_delta.to_definable
private instance subst_delta : 𝚫₁-Function₂[V] (subst ℒₛₑₜ) :=
  subst.defined.graph_delta.to_definable
private instance shift_delta : 𝚫₁-Function₁[V] (shift ℒₛₑₜ) :=
  shift.defined.graph_delta.to_definable
private instance len_delta : 𝚫₁-Function₁[V] (len : V→V) :=
  len_defined.graph_delta.to_definable

lemma encode_openAt {d p : V} (hp : IsSemiformula ℒₛₑₜ (d+1) p)
    (F B B' x fresh : V) (hB : Ext d B B' x) :
    encode (x∷F) B fresh (openAt d p)=encode F B' fresh p := by
  have he := ValidatorEnvironmentSubstitution254.encode_subst hp.shift (openingVec_typed d)
    (x∷F) B B' fresh (opening_matches d F B B' x hB)
  simpa only [openAt,encode_shift hp.isUFormula,tail_cons] using he

/-- The matrix identity used by the actual Foundation ALL rule. Source and
target contexts still require the separate formula-level alpha theorem. -/
lemma encode_free {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (F x fresh : V) :
    encode (x∷F) 0 fresh (free ℒₛₑₜ p)=encode F (x∷0) fresh p := by
  simpa [openAt,openingVec,free,substs1] using
    encode_openAt (d := 0) (by simpa using hp) F 0 (x∷0) x fresh (ext_zero x)

/-- The exact opened matrix occurring in the actual universal-introduction rule.
The starting binder is also the label placed at the free-environment head. -/
lemma encode_all_opened {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (F x : V) :
    encode F 0 x (^∀ p)=
      _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wal x
        (encode (x∷F) 0 (x+2) (free ℒₛₑₜ p)) := by
  rw [encode_all F 0 x hp.isUFormula,encode_free hp F x (x+2)]

lemma encode_exs_opened {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (F x : V) :
    encode F 0 x (^∃ p)=
      _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wim
        (_root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wal x
          (_root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wim
            (encode (x∷F) 0 (x+2) (free ℒₛₑₜ p)) 1)) 1 := by
  rw [encode_exs F 0 x hp.isUFormula,encode_free hp F x (x+2)]

end LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254
