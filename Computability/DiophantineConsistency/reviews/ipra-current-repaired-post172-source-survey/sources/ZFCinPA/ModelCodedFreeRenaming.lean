import ZFCinPA.ModelCodedBindOne

/-!
Two-counter free-variable renaming for internal syntax. The fixed graphs are
chosen before the arithmetic model. All indices, parameters and syntax codes
are internal. Bound labels are retained; free labels below `level` are
protected, and the remaining labels use the chosen-label/offset map.

The laws below isolate the SHIFT and ALL hygiene needed by a later bounded
proof-code induction. This module does not itself transport arbitrary internal
proofs, discharge ZF axiom closure, or prove a consistency comparison.
-/
namespace LeanProofs.ZFCinPA.ModelCodedFreeRenaming
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- On the unprotected tail this is `lift^level (η_chosen ∘ (+offset))`,
where η sends its chosen label to zero and sends every other label x to x+1.
The additive comparison avoids truncated subtraction in the fixed graph. -/
noncomputable def renameIndex (chosen level offset x : V) : V := by
  classical
  exact if x < level then x else if x+offset = level+chosen then level else x+offset+1

def renameIndexDef : 𝚺₁.Semisentence 5 := .mkSigma “out chosen level offset x.
  (x < level ∧ out = x) ∨
  (level ≤ x ∧ ((x+offset = level+chosen ∧ out = level) ∨
    (x+offset ≠ level+chosen ∧ out = x+offset+1)))”
instance renameIndex_defined :
    𝚺₁-Function₄[V] renameIndex via renameIndexDef := .mk fun e => by
  classical
  by_cases h : e 4 < e 2
  · simp [renameIndexDef,renameIndex,h,not_le.mpr h]
  · have hle : e 2 ≤ e 4 := le_of_not_gt h
    by_cases he : e 4+e 3 = e 2+e 1 <;>
      simp [renameIndexDef,renameIndex,h,hle,he]
instance renameIndex_definable : 𝚫₁-Function₄[V] renameIndex :=
  renameIndex_defined.graph_delta.to_definable

@[simp] lemma renameIndex_lift_zero (chosen level offset : V) :
    renameIndex chosen (level+1) offset 0 = 0 := by
  simp [renameIndex]
lemma renameIndex_lift_succ (chosen level offset x : V) :
    renameIndex chosen (level+1) offset (x+1) =
      renameIndex chosen level offset x+1 := by
  classical
  have hlt : x+1 < level+1 ↔ x < level := by simp
  have heq : (x+1)+offset = (level+1)+chosen ↔ x+offset = level+chosen := by
    constructor
    · intro h
      have h' : (x+offset)+1 = (level+chosen)+1 := by
        simpa only [add_assoc,add_comm,add_left_comm] using h
      exact add_right_cancel h'
    · intro h
      simpa only [add_assoc,add_comm,add_left_comm] using congrArg (fun z : V => z+1) h
  by_cases h : x < level <;> by_cases he : x+offset = level+chosen <;>
    simp only [renameIndex,hlt,heq,h,he,ite_true,ite_false]
  all_goals ac_rfl
lemma renameIndex_offset_succ (chosen offset x : V) :
    renameIndex chosen 0 offset (x+1) = renameIndex chosen 0 (offset+1) x := by
  classical
  simp [renameIndex,add_comm,add_left_comm]

namespace TermRenamer

def blueprint : Language.TermRec.Blueprint 3 where
  bvar := .mkSigma “out z chosen level offset. !qqBvarDef out z”
  fvar := .mkSigma “out x chosen level offset. ∃ y,
    !renameIndexDef y chosen level offset x ∧ !qqFvarDef out y”
  func := .mkSigma “out arity f oldArgs newArgs chosen level offset.
    !qqFuncDef out arity f newArgs”
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar _ z := ^#z
  fvar parameters x := ^&(renameIndex (parameters 0) (parameters 1) (parameters 2) x)
  func _ arity f _ newArgs := ^func arity f newArgs
  bvar_defined := .mk fun e => by simp [blueprint]
  fvar_defined := .mk fun e => by simp [blueprint]
  func_defined := .mk fun e => by simp [blueprint]
end TermRenamer

noncomputable def termRename (L : Language) [L.Encodable] [L.LORDefinable]
    (chosen level offset term : V) : V :=
  TermRenamer.construction.result L ![chosen,level,offset] term
noncomputable def termRenameVec (L : Language) [L.Encodable] [L.LORDefinable]
    (chosen level offset arity terms : V) : V :=
  TermRenamer.construction.resultVec L ![chosen,level,offset] arity terms
noncomputable def termRenameDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 5 :=
  (TermRenamer.blueprint.result L).rew (Rew.subst ![#0,#4,#1,#2,#3])
noncomputable def termRenameVecDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 6 :=
  (TermRenamer.blueprint.resultVec L).rew (Rew.subst ![#0,#4,#5,#1,#2,#3])
instance termRename_defined :
    𝚺₁-Function₄[V] (termRename L) via termRenameDef L := .mk fun e => by
  simpa [termRenameDef,termRename,Matrix.comp_vecCons'',Matrix.comp_vecCons']
    using (TermRenamer.construction.result_defined (L := L)).defined
      ![e 0,e 4,e 1,e 2,e 3]
instance termRenameVec_defined :
    𝚺₁-Function₅[V] (termRenameVec L) via termRenameVecDef L := .mk fun e => by
  simpa [termRenameVecDef,termRenameVec,Matrix.comp_vecCons'',Matrix.comp_vecCons']
    using (TermRenamer.construction.resultVec_defined (L := L)).defined
      ![e 0,e 4,e 5,e 1,e 2,e 3]
instance termRename_delta : 𝚫₁-Function₄[V] (termRename L) :=
  termRename_defined.graph_delta.to_definable
instance termRenameVec_delta : 𝚫₁.DefinableFunction₅ (termRenameVec (V := V) L) :=
  termRenameVec_defined.graph_delta.to_definable

@[simp] lemma termRename_bvar (chosen level offset z : V) :
    termRename L chosen level offset (^#z) = ^#z := by
  simp [termRename,TermRenamer.construction]
@[simp] lemma termRename_fvar (chosen level offset x : V) :
    termRename L chosen level offset (^&x) = ^&(renameIndex chosen level offset x) := by
  simp [termRename,TermRenamer.construction]
lemma termRename_func (chosen level offset : V) {arity f terms : V}
    (hf : L.IsFunc arity f) (ht : IsUTermVec L arity terms) :
    termRename L chosen level offset (^func arity f terms) =
      ^func arity f (termRenameVec L chosen level offset arity terms) := by
  simp [termRename,termRenameVec,TermRenamer.construction,hf,ht]
@[simp] lemma termRenameVec_lh (chosen level offset : V) {arity terms : V}
    (ht : IsUTermVec L arity terms) :
    len (termRenameVec L chosen level offset arity terms) = arity :=
  TermRenamer.construction.resultVec_lh L ![chosen,level,offset] ht
lemma nth_termRenameVec (chosen level offset : V) {arity terms i : V}
    (ht : IsUTermVec L arity terms) (hi : i < arity) :
    (termRenameVec L chosen level offset arity terms).[i] =
      termRename L chosen level offset terms.[i] :=
  TermRenamer.construction.nth_resultVec L ![chosen,level,offset] ht hi

lemma termRename_isSemiterm (chosen level offset : V) {depth term : V}
    (ht : IsSemiterm L depth term) :
    IsSemiterm L depth (termRename L chosen level offset term) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z hz; simpa
  · intro x; simp
  · intro arity f terms hf hv ih
    rw [termRename_func chosen level offset hf hv.isUTerm]
    refine IsSemiterm.func.mpr ⟨hf,?_⟩
    apply IsSemitermVec.iff.mpr
    refine ⟨termRenameVec_lh chosen level offset hv.isUTerm,?_⟩
    intro i hi
    rw [nth_termRenameVec chosen level offset hv.isUTerm hi]
    exact ih i hi
lemma termRenameVec_isSemiterm (chosen level offset : V) {depth arity terms : V}
    (ht : IsSemitermVec L arity depth terms) :
    IsSemitermVec L arity depth (termRenameVec L chosen level offset arity terms) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨termRenameVec_lh chosen level offset ht.isUTerm,?_⟩
  intro i hi
  rw [nth_termRenameVec chosen level offset ht.isUTerm hi]
  exact termRename_isSemiterm chosen level offset (ht.nth hi)

lemma termRename_isUTerm (chosen level offset : V) {term : V} (ht : IsUTerm L term) :
    IsUTerm L (termRename L chosen level offset term) :=
  (termRename_isSemiterm chosen level offset ht.isSemiterm).isUTerm
lemma termRenameVec_isUTerm (chosen level offset : V) {arity terms : V}
    (ht : IsUTermVec L arity terms) :
    IsUTermVec L arity (termRenameVec L chosen level offset arity terms) :=
  (termRenameVec_isSemiterm chosen level offset ht.isSemitermVec).isUTerm

namespace FormulaRenamer
noncomputable def blueprint (L : Language) [L.Encodable] [L.LORDefinable] :
    UformulaRec1.Blueprint where
  rel := .mkSigma “out state arity R terms. ∃ chosen, !pi₁Def chosen state ∧
    ∃ rest, !pi₂Def rest state ∧ ∃ level, !pi₁Def level rest ∧
    ∃ offset, !pi₂Def offset rest ∧ ∃ args,
    !(termRenameVecDef L) args chosen level offset arity terms ∧ !qqRelDef out arity R args”
  nrel := .mkSigma “out state arity R terms. ∃ chosen, !pi₁Def chosen state ∧
    ∃ rest, !pi₂Def rest state ∧ ∃ level, !pi₁Def level rest ∧
    ∃ offset, !pi₂Def offset rest ∧ ∃ args,
    !(termRenameVecDef L) args chosen level offset arity terms ∧ !qqNRelDef out arity R args”
  verum := .mkSigma “out state. !qqVerumDef out”
  falsum := .mkSigma “out state. !qqFalsumDef out”
  and := .mkSigma “out state p q left right. !qqAndDef out left right”
  or := .mkSigma “out state p q left right. !qqOrDef out left right”
  all := .mkSigma “out state p body. !qqAllDef out body”
  exs := .mkSigma “out state p body. !qqExsDef out body”
  allChanges := .mkSigma “next state. next = state”
  exsChanges := .mkSigma “next state. next = state”
noncomputable def construction (L : Language) [L.Encodable] [L.LORDefinable] :
    UformulaRec1.Construction V (blueprint L) where
  rel state arity R terms :=
    ^rel arity R (termRenameVec L (π₁ state) (π₁ (π₂ state)) (π₂ (π₂ state)) arity terms)
  nrel state arity R terms :=
    ^nrel arity R (termRenameVec L (π₁ state) (π₁ (π₂ state)) (π₂ (π₂ state)) arity terms)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ left right := left ^⋏ right
  or _ _ _ left right := left ^⋎ right
  all _ _ body := ^∀ body
  exs _ _ body := ^∃ body
  allChanges state := state
  exsChanges state := state
  rel_defined := .mk fun e => by simp [blueprint]
  nrel_defined := .mk fun e => by simp [blueprint]
  verum_defined := .mk fun e => by simp [blueprint]
  falsum_defined := .mk fun e => by simp [blueprint]
  and_defined := .mk fun e => by simp [blueprint]
  or_defined := .mk fun e => by simp [blueprint]
  all_defined := .mk fun e => by simp [blueprint]
  exs_defined := .mk fun e => by simp [blueprint]
  allChanges_defined := .mk fun e => by simp [blueprint]
  exChanges_defined := .mk fun e => by simp [blueprint]
end FormulaRenamer

noncomputable def rename (L : Language) [L.Encodable] [L.LORDefinable]
    (chosen level offset formula : V) : V :=
  (FormulaRenamer.construction L).result L ⟪chosen,⟪level,offset⟫⟫ formula
noncomputable def rawRenameDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 3 := (FormulaRenamer.blueprint L).result L
noncomputable def renameDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 5 := .mkSigma “out chosen level offset formula.
      ∃ rest, !pairDef rest level offset ∧ ∃ state, !pairDef state chosen rest ∧
      !(rawRenameDef L) out state formula”
instance rename_defined :
    𝚺₁-Function₄[V] (rename L) via renameDef L := .mk fun e => by
  simpa [renameDef,rawRenameDef,rename]
    using (FormulaRenamer.construction L).result_defined.defined
      ![e 0,⟪e 1,⟪e 2,e 3⟫⟫,e 4]
instance rename_delta : 𝚫₁-Function₄[V] (rename L) :=
  rename_defined.graph_delta.to_definable

lemma rename_rel (chosen level offset : V) {arity R terms : V}
    (hR : L.IsRel arity R) (ht : IsUTermVec L arity terms) :
    rename L chosen level offset (^rel arity R terms) =
      ^rel arity R (termRenameVec L chosen level offset arity terms) := by
  simp [rename,FormulaRenamer.construction,hR,ht]
lemma rename_nrel (chosen level offset : V) {arity R terms : V}
    (hR : L.IsRel arity R) (ht : IsUTermVec L arity terms) :
    rename L chosen level offset (^nrel arity R terms) =
      ^nrel arity R (termRenameVec L chosen level offset arity terms) := by
  simp [rename,FormulaRenamer.construction,hR,ht]
@[simp] lemma rename_verum (chosen level offset : V) :
    rename L chosen level offset ^⊤ = ^⊤ := by
  simp [rename,FormulaRenamer.construction]
@[simp] lemma rename_falsum (chosen level offset : V) :
    rename L chosen level offset ^⊥ = ^⊥ := by
  simp [rename,FormulaRenamer.construction]
lemma rename_and (chosen level offset : V) {p q : V}
    (hp : IsUFormula L p) (hq : IsUFormula L q) :
    rename L chosen level offset (p ^⋏ q) =
      rename L chosen level offset p ^⋏ rename L chosen level offset q := by
  simp [rename,FormulaRenamer.construction,hp,hq]
lemma rename_or (chosen level offset : V) {p q : V}
    (hp : IsUFormula L p) (hq : IsUFormula L q) :
    rename L chosen level offset (p ^⋎ q) =
      rename L chosen level offset p ^⋎ rename L chosen level offset q := by
  simp [rename,FormulaRenamer.construction,hp,hq]
lemma rename_all (chosen level offset : V) {p : V} (hp : IsUFormula L p) :
    rename L chosen level offset (^∀ p) = ^∀ (rename L chosen level offset p) := by
  simp [rename,FormulaRenamer.construction,hp]
lemma rename_exs (chosen level offset : V) {p : V} (hp : IsUFormula L p) :
    rename L chosen level offset (^∃ p) = ^∃ (rename L chosen level offset p) := by
  simp [rename,FormulaRenamer.construction,hp]

lemma rename_isSemiformula (chosen level offset : V) {depth p : V}
    (hp : IsSemiformula L depth p) :
    IsSemiformula L depth (rename L chosen level offset p) := by
  apply IsSemiformula.sigma1_structural_induction (P := fun depth p =>
    IsSemiformula L depth (rename L chosen level offset p))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  all_goals
    intros
    simp (discharger := aesop (add safe [IsSemitermVec.isUTerm, IsSemiformula.isUFormula]))
      [*, rename_rel, rename_nrel, termRenameVec_isSemiterm,
        rename_and, rename_or, rename_all, rename_exs,
        IsSemiformula.rel, IsSemiformula.nrel, IsSemiformula.and, IsSemiformula.or]

lemma rename_isUFormula (chosen level offset : V) {p : V} (hp : IsUFormula L p) :
    IsUFormula L (rename L chosen level offset p) :=
  (rename_isSemiformula chosen level offset hp.isSemiformula).isUFormula

lemma termRename_shift_lift (chosen level offset : V) {term : V} (ht : IsUTerm L term) :
    termRename L chosen (level+1) offset (termShift L term) =
      termShift L (termRename L chosen level offset term) := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z; simp
  · intro x; simp [renameIndex_lift_succ]
  · intro arity f terms hf hv ih
    rw [termShift_func hf hv,
      termRename_func chosen (level+1) offset hf hv.termShiftVec]
    rw [termRename_func chosen level offset hf hv,
      termShift_func hf (termRenameVec_isUTerm chosen level offset hv)]
    apply congrArg (fun args => ^func arity f args)
    apply nth_ext' arity
    · simp [hv]
    · simp [hv,termRenameVec_isUTerm]
    · intro i hi
      rw [nth_termRenameVec chosen (level+1) offset hv.termShiftVec hi,
        nth_termShiftVec hv hi]
      rw [nth_termShiftVec (termRenameVec_isUTerm chosen level offset hv) hi,
        nth_termRenameVec chosen level offset hv hi]
      exact ih i hi
lemma termRenameVec_shift_lift (chosen level offset : V) {arity terms : V}
    (ht : IsUTermVec L arity terms) :
    termRenameVec L chosen (level+1) offset arity (termShiftVec L arity terms) =
      termShiftVec L arity (termRenameVec L chosen level offset arity terms) := by
  apply nth_ext' arity
  · simp [ht]
  · simp [ht,termRenameVec_isUTerm]
  · intro i hi
    rw [nth_termRenameVec chosen (level+1) offset ht.termShiftVec hi,
      nth_termShiftVec ht hi]
    rw [nth_termShiftVec (termRenameVec_isUTerm chosen level offset ht) hi,
      nth_termRenameVec chosen level offset ht hi]
    exact termRename_shift_lift chosen level offset (ht.nth hi)
/-- Positive-level SHIFT commutation. -/
lemma rename_shift_lift (chosen level offset : V) {p : V} (hp : IsUFormula L p) :
    rename L chosen (level+1) offset (shift L p) = shift L (rename L chosen level offset p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  all_goals
    intros
    simp_all [shift_rel, shift_nrel, rename_rel, rename_nrel, termRenameVec_shift_lift,
      termRenameVec_isUTerm, shift_and, shift_or, rename_and, rename_or,
      rename_isUFormula, shift_all, shift_exs, rename_all, rename_exs]

lemma termRename_shift_offset (chosen offset : V) {term : V} (ht : IsUTerm L term) :
    termRename L chosen 0 offset (termShift L term) =
      termRename L chosen 0 (offset+1) term := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z; simp
  · intro x; simp [renameIndex_offset_succ]
  · intro arity f terms hf hv ih
    rw [termShift_func hf hv,
      termRename_func chosen 0 offset hf hv.termShiftVec]
    rw [termRename_func chosen 0 (offset+1) hf hv]
    apply congrArg (fun args => ^func arity f args)
    apply nth_ext' arity
    · simp [hv]
    · simp [hv]
    · intro i hi
      rw [nth_termRenameVec chosen 0 offset hv.termShiftVec hi,
        nth_termShiftVec hv hi]
      rw [nth_termRenameVec chosen 0 (offset+1) hv hi]
      exact ih i hi
lemma termRenameVec_shift_offset (chosen offset : V) {arity terms : V}
    (ht : IsUTermVec L arity terms) :
    termRenameVec L chosen 0 offset arity (termShiftVec L arity terms) =
      termRenameVec L chosen 0 (offset+1) arity terms := by
  apply nth_ext' arity
  · simp [ht]
  · simp [ht]
  · intro i hi
    rw [nth_termRenameVec chosen 0 offset ht.termShiftVec hi,
      nth_termShiftVec ht hi]
    rw [nth_termRenameVec chosen 0 (offset+1) ht hi]
    exact termRename_shift_offset chosen offset (ht.nth hi)
/-- The level-zero SHIFT case consumes one offset instead of requiring an inverse SHIFT. -/
lemma rename_shift_offset (chosen offset : V) {p : V} (hp : IsUFormula L p) :
    rename L chosen 0 offset (shift L p) = rename L chosen 0 (offset+1) p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  all_goals
    intros
    simp_all [shift_rel, shift_nrel, rename_rel, rename_nrel, termRenameVec_shift_offset,
      shift_and, shift_or, rename_and, rename_or, shift_all, shift_exs, rename_all, rename_exs]

lemma termRename_bShift (chosen level offset : V) {term : V} (ht : IsUTerm L term) :
    termRename L chosen level offset (termBShift L term) =
      termBShift L (termRename L chosen level offset term) := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro arity f terms hf hv ih
    rw [termBShift_func hf hv,
      termRename_func chosen level offset hf hv.isSemitermVec.termBShiftVec.isUTerm,
      termRename_func chosen level offset hf hv,
      termBShift_func hf (termRenameVec_isUTerm chosen level offset hv)]
    apply congrArg (fun args => ^func arity f args)
    apply nth_ext' arity
    · exact termRenameVec_lh chosen level offset hv.isSemitermVec.termBShiftVec.isUTerm
    · simp [hv,termRenameVec_isUTerm]
    · intro i hi
      rw [nth_termRenameVec chosen level offset hv.isSemitermVec.termBShiftVec.isUTerm hi,
        nth_termBShiftVec hv hi,
        nth_termBShiftVec (termRenameVec_isUTerm chosen level offset hv) hi,
        nth_termRenameVec chosen level offset hv hi]
      exact ih i hi
lemma termRename_qVec (chosen level offset : V) {n m vector : V}
    (hw : IsSemitermVec L n m vector) :
    termRenameVec L chosen level offset (n+1) (qVec L vector) =
      qVec L (termRenameVec L chosen level offset n vector) := by
  apply nth_ext' (n+1)
  · exact termRenameVec_lh chosen level offset hw.qVec.isUTerm
  · exact len_qVec (termRenameVec_isUTerm chosen level offset hw.isUTerm)
  · intro i hi
    rw [nth_termRenameVec chosen level offset hw.qVec.isUTerm hi]
    rcases zero_or_succ i with rfl | ⟨i,rfl⟩
    · simp [Bootstrapping.qVec]
    · have hin : i < n := by simpa using hi
      simp only [Bootstrapping.qVec,nth_adjoin_succ,hw.lh,
        termRenameVec_lh chosen level offset hw.isUTerm]
      rw [nth_termBShiftVec hw.isUTerm hin,
        nth_termBShiftVec (termRenameVec_isUTerm chosen level offset hw.isUTerm)
          (by simpa using hin),
        nth_termRenameVec chosen level offset hw.isUTerm hin,
        termRename_bShift chosen level offset (hw.nth hin).isUTerm]

lemma termRename_subst (chosen level offset : V) {n m term vector : V}
    (ht : IsSemiterm L n term) (hw : IsSemitermVec L n m vector) :
    termRename L chosen level offset (termSubst L vector term) =
      termSubst L (termRenameVec L chosen level offset n vector)
        (termRename L chosen level offset term) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z hz
    simp [termSubst_bvar,nth_termRenameVec chosen level offset hw.isUTerm hz]
  · intro x; simp
  · intro arity f terms hf hv ih
    rw [termSubst_func hf hv.isUTerm,
      termRename_func chosen level offset hf (hw.termSubstVec hv).isUTerm,
      termRename_func chosen level offset hf hv.isUTerm,
      termSubst_func hf (termRenameVec_isUTerm chosen level offset hv.isUTerm)]
    apply congrArg (fun args => ^func arity f args)
    apply nth_ext' arity
    · exact termRenameVec_lh chosen level offset (hw.termSubstVec hv).isUTerm
    · simp [termRenameVec_isUTerm chosen level offset hv.isUTerm]
    · intro i hi
      rw [nth_termRenameVec chosen level offset (hw.termSubstVec hv).isUTerm hi,
        nth_termSubstVec hv.isUTerm hi,
        nth_termSubstVec (termRenameVec_isUTerm chosen level offset hv.isUTerm) hi,
        nth_termRenameVec chosen level offset hv.isUTerm hi]
      exact ih i hi
lemma termRenameVec_subst (chosen level offset : V) {n m arity terms vector : V}
    (ht : IsSemitermVec L arity n terms) (hw : IsSemitermVec L n m vector) :
    termRenameVec L chosen level offset arity (termSubstVec L arity vector terms) =
      termSubstVec L arity (termRenameVec L chosen level offset n vector)
        (termRenameVec L chosen level offset arity terms) := by
  apply nth_ext' arity
  · exact termRenameVec_lh chosen level offset (hw.termSubstVec ht).isUTerm
  · simp [termRenameVec_isUTerm chosen level offset ht.isUTerm]
  · intro i hi
    rw [nth_termRenameVec chosen level offset (hw.termSubstVec ht).isUTerm hi,
      nth_termSubstVec ht.isUTerm hi,
      nth_termSubstVec (termRenameVec_isUTerm chosen level offset ht.isUTerm) hi,
      nth_termRenameVec chosen level offset ht.isUTerm hi]
    exact termRename_subst chosen level offset (ht.nth hi) hw

lemma rename_subst (chosen level offset : V) {n p : V} (hp : IsSemiformula L n p) :
    ∀ m vector : V, IsSemitermVec L n m vector →
    rename L chosen level offset (subst L vector p) =
      subst L (termRenameVec L chosen level offset n vector)
        (rename L chosen level offset p) := by
  apply IsSemiformula.pi1_structural_induction (P := fun n p =>
    ∀ m vector : V, IsSemitermVec L n m vector →
    rename L chosen level offset (subst L vector p) =
      subst L (termRenameVec L chosen level offset n vector)
        (rename L chosen level offset p))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  all_goals
    intros
    simp (discharger := aesop (add safe [IsSemitermVec.isUTerm, IsSemiformula.isUFormula,
      IsSemiformula.subst, IsSemitermVec.qVec, IsSemitermVec.termSubstVec,
      termRenameVec_isUTerm, rename_isUFormula]))
      [*, substs_rel, substs_nrel, substs_and, substs_or, substs_all, substs_ex,
        rename_rel, rename_nrel, rename_and, rename_or, rename_all, rename_exs,
        termRenameVec_subst, termRename_qVec]

lemma termRenameVec_singleton (chosen level offset : V) {term : V} (ht : IsUTerm L term) :
    termRenameVec L chosen level offset 1 (term ∷ 0) =
      termRename L chosen level offset term ∷ 0 := by
  apply nth_ext' 1
  · simp [ht]
  · simp
  · intro i hi
    have : i = 0 := by simpa using hi
    subst i
    simp [nth_termRenameVec,ht]

/-- ALL/eigenvariable commutation, including arbitrary internal free parameters. -/
lemma rename_free_lift (chosen level offset : V) {p : V} (hp : IsSemiformula L 1 p) :
    rename L chosen (level+1) offset (free L p) =
      free L (rename L chosen level offset p) := by
  unfold free substs1
  rw [rename_subst chosen (level+1) offset hp.shift 0 (^&0 ∷ 0) (by simp),
    termRenameVec_singleton chosen (level+1) offset (by simp),
    termRename_fvar,renameIndex_lift_zero,rename_shift_lift chosen level offset hp.isUFormula]

/-- Internal shift-fixed terms have no observable free labels for this renaming. -/
lemma termRename_of_shift_fixed (chosen level offset : V) {term : V}
    (ht : IsUTerm L term) : termShift L term = term →
    termRename L chosen level offset term = term := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z _; simp
  · intro x h
    have : x+1 = x := by simpa only [termShift_fvar,qqFvar_inj] using h
    exact False.elim (by simp at this)
  · intro arity f terms hf hv ih h
    have hvfix : termShiftVec L arity terms = terms := by
      simpa only [termShift_func hf hv,qqFunc_inj,true_and] using h
    rw [termRename_func chosen level offset hf hv]
    apply congrArg (fun args => ^func arity f args)
    apply nth_ext' arity
    · simp [hv]
    · exact hv.lh.symm
    · intro i hi
      rw [nth_termRenameVec chosen level offset hv hi]
      apply ih i hi
      have := congrArg (fun args : V => args.[i]) hvfix
      simpa only [nth_termShiftVec hv hi] using this
lemma termRenameVec_of_shift_fixed (chosen level offset : V) {arity terms : V}
    (ht : IsUTermVec L arity terms) (h : termShiftVec L arity terms = terms) :
    termRenameVec L chosen level offset arity terms = terms := by
  apply nth_ext' arity
  · simp [ht]
  · exact ht.lh.symm
  · intro i hi
    rw [nth_termRenameVec chosen level offset ht hi]
    apply termRename_of_shift_fixed chosen level offset (ht.nth hi)
    have := congrArg (fun args : V => args.[i]) h
    simpa only [nth_termShiftVec ht hi] using this

/-- This is an internal syntax theorem, not an external standard-code argument. -/
lemma rename_of_shift_fixed (chosen level offset : V) {p : V} (hp : IsUFormula L p) :
    shift L p = p → rename L chosen level offset p = p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  all_goals
    intros
    simp_all [shift_rel, shift_nrel, qqRel_inj, qqNRel_inj,
      rename_rel, rename_nrel, termRenameVec_of_shift_fixed,
      shift_and, shift_or, qqAnd_inj, qqOr_inj, rename_and, rename_or,
      shift_all, shift_exs, qqAll_inj, qqExs_inj, rename_all, rename_exs]

lemma rename_neg (chosen level offset : V) {p : V} (hp : IsUFormula L p) :
    rename L chosen level offset (neg L p) = neg L (rename L chosen level offset p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  all_goals
    intros
    simp_all [rename_rel, rename_nrel, termRenameVec_isUTerm,
      rename_and, rename_or, rename_isUFormula, rename_all, rename_exs]

end LeanProofs.ZFCinPA.ModelCodedFreeRenaming
