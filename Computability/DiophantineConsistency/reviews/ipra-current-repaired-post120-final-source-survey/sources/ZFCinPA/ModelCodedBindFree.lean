import ZFCinPA.Instances
import ZFCinPA.SchemaClosure

/-!
All-internal closing traversal. At binder depth d, free label x becomes
bound label d+x; existing bound labels are retained. The fixed graphs precede
the arithmetic model. Shift-fixedness and inverse substitution hold for
arbitrary internal depths and opening vectors, including nonstandard codes.
This does not perform repeated proof specialization or consistency transport.
-/
namespace LeanProofs.ZFCinPA.ModelCodedBindFree
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace TermBinder

def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “out z depth. !qqBvarDef out z”
  fvar := .mkSigma “out x depth. !qqBvarDef out (depth+x)”
  func := .mkSigma “out k f oldArgs newArgs depth. !qqFuncDef out k f newArgs”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar _ z := ^#z
  fvar parameters x := ^#(parameters 0+x)
  func _ k f _ newArgs := ^func k f newArgs
  bvar_defined := .mk fun e => by simp [blueprint]
  fvar_defined := .mk fun e => by simp [blueprint]
  func_defined := .mk fun e => by simp [blueprint]

end TermBinder

noncomputable def termBindFreeAt (L : Language) [L.Encodable] [L.LORDefinable]
    (depth term : V) : V := TermBinder.construction.result L ![depth] term
noncomputable def termBindFreeVecAt (L : Language) [L.Encodable] [L.LORDefinable]
    (depth arity terms : V) : V := TermBinder.construction.resultVec L ![depth] arity terms

noncomputable def termBindFreeAtDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 3 :=
  (TermBinder.blueprint.result L).rew (Rew.subst ![#0,#2,#1])
noncomputable def termBindFreeVecAtDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 4 :=
  (TermBinder.blueprint.resultVec L).rew (Rew.subst ![#0,#2,#3,#1])

instance termBindFreeAt_defined :
    𝚺₁-Function₂[V] (termBindFreeAt L) via termBindFreeAtDef L := .mk fun e => by
  simpa [termBindFreeAtDef,termBindFreeAt,Matrix.comp_vecCons',Matrix.constant_eq_singleton]
    using TermBinder.construction.result_defined.defined ![e 0,e 2,e 1]
instance termBindFreeVecAt_defined :
    𝚺₁-Function₃[V] (termBindFreeVecAt L) via termBindFreeVecAtDef L := .mk fun e => by
  simpa [termBindFreeVecAtDef,termBindFreeVecAt,Matrix.comp_vecCons',Matrix.constant_eq_singleton]
    using TermBinder.construction.resultVec_defined.defined ![e 0,e 2,e 3,e 1]

namespace FormulaBinder

noncomputable def blueprint (L : Language) [L.Encodable] [L.LORDefinable] :
    UformulaRec1.Blueprint where
  rel := .mkSigma “out depth k R terms. ∃ args,
    !(termBindFreeVecAtDef L) args depth k terms ∧ !qqRelDef out k R args”
  nrel := .mkSigma “out depth k R terms. ∃ args,
    !(termBindFreeVecAtDef L) args depth k terms ∧ !qqNRelDef out k R args”
  verum := .mkSigma “out depth. !qqVerumDef out”
  falsum := .mkSigma “out depth. !qqFalsumDef out”
  and := .mkSigma “out depth p q left right. !qqAndDef out left right”
  or := .mkSigma “out depth p q left right. !qqOrDef out left right”
  all := .mkSigma “out depth p body. !qqAllDef out body”
  exs := .mkSigma “out depth p body. !qqExsDef out body”
  allChanges := .mkSigma “next depth. next = depth+1”
  exsChanges := .mkSigma “next depth. next = depth+1”

noncomputable def construction (L : Language) [L.Encodable] [L.LORDefinable] :
    UformulaRec1.Construction V (blueprint L) where
  rel depth k R terms := ^rel k R (termBindFreeVecAt L depth k terms)
  nrel depth k R terms := ^nrel k R (termBindFreeVecAt L depth k terms)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ left right := left ^⋏ right
  or _ _ _ left right := left ^⋎ right
  all _ _ body := ^∀ body
  exs _ _ body := ^∃ body
  allChanges depth := depth+1
  exsChanges depth := depth+1
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

end FormulaBinder

noncomputable def bindFreeAt (L : Language) [L.Encodable] [L.LORDefinable]
    (depth formula : V) : V := (FormulaBinder.construction L).result L depth formula
noncomputable def bindFreeAtDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 3 := (FormulaBinder.blueprint L).result L
instance bindFreeAt_defined :
    𝚺₁-Function₂[V] (bindFreeAt L) via bindFreeAtDef L :=
  (FormulaBinder.construction L).result_defined

private instance termBindFreeAt_delta : 𝚫₁-Function₂[V] (termBindFreeAt L) :=
  termBindFreeAt_defined.graph_delta.to_definable
private instance termBindFreeVecAt_delta : 𝚫₁-Function₃[V] (termBindFreeVecAt L) :=
  termBindFreeVecAt_defined.graph_delta.to_definable
private instance bindFreeAt_delta : 𝚫₁-Function₂[V] (bindFreeAt L) :=
  bindFreeAt_defined.graph_delta.to_definable

@[simp] lemma termBindFreeAt_bvar (depth z : V) :
    termBindFreeAt L depth (^#z) = ^#z := by
  simp [termBindFreeAt, TermBinder.construction]
@[simp] lemma termBindFreeAt_fvar (depth x : V) :
    termBindFreeAt L depth (^&x) = ^#(depth+x) := by
  simp [termBindFreeAt, TermBinder.construction]
lemma termBindFreeAt_func (depth : V) {k f terms : V}
    (hf : L.IsFunc k f) (ht : IsUTermVec L k terms) :
    termBindFreeAt L depth (^func k f terms) =
      ^func k f (termBindFreeVecAt L depth k terms) := by
  simp [termBindFreeAt,termBindFreeVecAt,TermBinder.construction,hf,ht]

@[simp] lemma termBindFreeVecAt_lh (depth : V) {k terms : V}
    (ht : IsUTermVec L k terms) : len (termBindFreeVecAt L depth k terms) = k :=
  TermBinder.construction.resultVec_lh L ![depth] ht
lemma nth_termBindFreeVecAt (depth : V) {k terms i : V}
    (ht : IsUTermVec L k terms) (hi : i < k) :
    (termBindFreeVecAt L depth k terms).[i] = termBindFreeAt L depth terms.[i] :=
  TermBinder.construction.nth_resultVec L ![depth] ht hi

private lemma termBindFreeAt_wf_shift (depth : V) {term : V} (ht : IsUTerm L term) :
    IsUTerm L (termBindFreeAt L depth term) ∧
      termShift L (termBindFreeAt L depth term) = termBindFreeAt L depth term := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f terms hf hv ih
    have hargs : IsUTermVec L k (termBindFreeVecAt L depth k terms) := by
      refine ⟨(termBindFreeVecAt_lh depth hv).symm, ?_⟩
      intro i hi
      rw [nth_termBindFreeVecAt depth hv hi]
      exact (ih i hi).1
    have hshift : termShiftVec L k (termBindFreeVecAt L depth k terms) =
        termBindFreeVecAt L depth k terms := by
      apply nth_ext' k
      · simp [hargs]
      · simp [hv]
      · intro i hi
        rw [nth_termShiftVec hargs hi, nth_termBindFreeVecAt depth hv hi]
        exact (ih i hi).2
    rw [termBindFreeAt_func depth hf hv]
    constructor
    · exact IsUTerm.func_iff.mpr ⟨hf, hargs⟩
    · rw [termShift_func hf hargs, hshift]

lemma termBindFreeAt_isUTerm (depth : V) {term : V} (ht : IsUTerm L term) :
    IsUTerm L (termBindFreeAt L depth term) := (termBindFreeAt_wf_shift depth ht).1

lemma termBindFreeVecAt_isUTerm (depth : V) {k terms : V}
    (ht : IsUTermVec L k terms) : IsUTermVec L k (termBindFreeVecAt L depth k terms) := by
  refine ⟨(termBindFreeVecAt_lh depth ht).symm, ?_⟩
  intro i hi
  rw [nth_termBindFreeVecAt depth ht hi]
  exact termBindFreeAt_isUTerm depth (ht.nth hi)

lemma termBindFreeAt_shift_fixed (depth : V) {term : V} (ht : IsUTerm L term) :
    termShift L (termBindFreeAt L depth term) = termBindFreeAt L depth term :=
  (termBindFreeAt_wf_shift depth ht).2

lemma termBindFreeVecAt_shift_fixed (depth : V) {k terms : V}
    (ht : IsUTermVec L k terms) :
    termShiftVec L k (termBindFreeVecAt L depth k terms) =
      termBindFreeVecAt L depth k terms := by
  apply nth_ext' k
  · simp [termBindFreeVecAt_isUTerm depth ht]
  · simp [ht]
  · intro i hi
    rw [nth_termShiftVec (termBindFreeVecAt_isUTerm depth ht) hi,
      nth_termBindFreeVecAt depth ht hi]
    exact termBindFreeAt_shift_fixed depth (ht.nth hi)

lemma bindFreeAt_rel (depth : V) {k R terms : V}
    (hR : L.IsRel k R) (ht : IsUTermVec L k terms) :
    bindFreeAt L depth (^rel k R terms) = ^rel k R (termBindFreeVecAt L depth k terms) := by
  simp [bindFreeAt, FormulaBinder.construction,hR,ht]
lemma bindFreeAt_nrel (depth : V) {k R terms : V}
    (hR : L.IsRel k R) (ht : IsUTermVec L k terms) :
    bindFreeAt L depth (^nrel k R terms) = ^nrel k R (termBindFreeVecAt L depth k terms) := by
  simp [bindFreeAt, FormulaBinder.construction,hR,ht]
@[simp] lemma bindFreeAt_verum (depth : V) : bindFreeAt L depth ^⊤ = ^⊤ := by
  simp [bindFreeAt,FormulaBinder.construction]
@[simp] lemma bindFreeAt_falsum (depth : V) : bindFreeAt L depth ^⊥ = ^⊥ := by
  simp [bindFreeAt,FormulaBinder.construction]
lemma bindFreeAt_and (depth : V) {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bindFreeAt L depth (p ^⋏ q) = bindFreeAt L depth p ^⋏ bindFreeAt L depth q := by
  simp [bindFreeAt,FormulaBinder.construction,hp,hq]
lemma bindFreeAt_or (depth : V) {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bindFreeAt L depth (p ^⋎ q) = bindFreeAt L depth p ^⋎ bindFreeAt L depth q := by
  simp [bindFreeAt,FormulaBinder.construction,hp,hq]
lemma bindFreeAt_all (depth : V) {p : V} (hp : IsUFormula L p) :
    bindFreeAt L depth (^∀ p) = ^∀ (bindFreeAt L (depth+1) p) := by
  simp [bindFreeAt,FormulaBinder.construction,hp]
lemma bindFreeAt_exs (depth : V) {p : V} (hp : IsUFormula L p) :
    bindFreeAt L depth (^∃ p) = ^∃ (bindFreeAt L (depth+1) p) := by
  simp [bindFreeAt,FormulaBinder.construction,hp]

private lemma bindFreeAt_wf_shift {p : V} (hp : IsUFormula L p) :
    ∀ depth : V, IsUFormula L (bindFreeAt L depth p) ∧
      shift L (bindFreeAt L depth p) = bindFreeAt L depth p := by
  apply IsUFormula.ISigma1.pi1_succ_induction (P := fun p => ∀ depth : V,
    IsUFormula L (bindFreeAt L depth p) ∧ shift L (bindFreeAt L depth p) = bindFreeAt L depth p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  all_goals
    intros
    simp_all [forall_and, bindFreeAt_rel, bindFreeAt_nrel, bindFreeAt_and, bindFreeAt_or,
      bindFreeAt_all, bindFreeAt_exs, termBindFreeVecAt_isUTerm, termBindFreeVecAt_shift_fixed,
      shift_rel, shift_nrel, shift_and, shift_or, shift_all, shift_exs]

lemma bindFreeAt_isUFormula {p : V} (hp : IsUFormula L p) :
    ∀ depth : V, IsUFormula L (bindFreeAt L depth p) := fun depth => (bindFreeAt_wf_shift hp depth).1

lemma bindFreeAt_shift_fixed {p : V} (hp : IsUFormula L p) :
    ∀ depth : V, shift L (bindFreeAt L depth p) = bindFreeAt L depth p :=
  fun depth => (bindFreeAt_wf_shift hp depth).2

/-- Preserve existing bound slots and reopen new slots to their original free labels.
All ranges are internal bounded ranges; none is a metatheoretic Fin arity. -/
def Opening (depth slots vector : V) : Prop :=
  depth ≤ slots ∧ (∀ i < depth, vector.[i] = ^#i) ∧
    (∀ x < slots, depth+x < slots → vector.[depth+x] = ^&x)
private instance opening_definable : 𝚫₁-Relation₃[V] (Opening (V := V)) := by
  unfold Opening
  definability

lemma Opening.qVec {depth slots vector : V}
    (ho : Opening depth slots vector) (hw : IsSemitermVec L slots depth vector) :
    Opening (depth+1) (slots+1) (qVec L vector) := by
  refine ⟨by simpa using ho.1, ?_, ?_⟩
  · intro i hi
    rcases zero_or_succ i with rfl | ⟨i,rfl⟩
    · simp [Bootstrapping.qVec]
    · have hid : i < depth := by simpa using hi
      have him : i < slots := lt_of_lt_of_le hid ho.1
      simp only [Bootstrapping.qVec,hw.lh,nth_adjoin_succ]
      rw [nth_termBShiftVec hw.isUTerm him,ho.2.1 i hid]
      simp
  · intro x hx hix
    have hix' : depth+x < slots := by
      have hh := hix
      rw [add_right_comm depth 1 x] at hh
      simpa using hh
    have hx' : x < slots := lt_of_le_of_lt (by simp) hix'
    rw [show depth+1+x = (depth+x)+1 by exact add_right_comm _ _ _]
    simp only [Bootstrapping.qVec,hw.lh,nth_adjoin_succ]
    rw [nth_termBShiftVec hw.isUTerm hix',ho.2.2 x hx' hix']
    simp

lemma termBindFreeAt_inverse {depth term : V} (ht : IsSemiterm L depth term) :
    ∀ slots vector : V, IsSemitermVec L slots depth vector →
      IsSemiterm L slots (termBindFreeAt L depth term) → Opening depth slots vector →
      termSubst L vector (termBindFreeAt L depth term) = term := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z hz slots vector hw hb ho
    rw [termBindFreeAt_bvar,termSubst_bvar]
    exact ho.2.1 z hz
  · intro x slots vector hw hb ho
    have hdx : depth+x < slots := by simpa using hb
    have hx : x < slots := lt_of_le_of_lt (by simp) hdx
    rw [termBindFreeAt_fvar,termSubst_bvar]
    exact ho.2.2 x hx hdx
  · intro k f terms hf hv ih slots vector hw hb ho
    have hv' : IsSemitermVec L k slots (termBindFreeVecAt L depth k terms) := by
      exact (IsSemiterm.func.mp (by simpa [termBindFreeAt_func depth hf hv.isUTerm] using hb)).2
    rw [termBindFreeAt_func depth hf hv.isUTerm,termSubst_func hf hv'.isUTerm]
    apply congrArg (fun args => ^func k f args)
    apply nth_ext' k
    · simp [hv'.isUTerm]
    · exact hv.lh
    · intro i hi
      rw [nth_termSubstVec hv'.isUTerm hi,nth_termBindFreeVecAt depth hv.isUTerm hi]
      apply ih i hi slots vector hw
      · simpa [nth_termBindFreeVecAt depth hv.isUTerm hi] using hv'.nth hi
      · exact ho

lemma termBindFreeVecAt_inverse {depth slots vector k terms : V}
    (ht : IsSemitermVec L k depth terms)
    (hw : IsSemitermVec L slots depth vector)
    (hb : IsSemitermVec L k slots (termBindFreeVecAt L depth k terms))
    (ho : Opening depth slots vector) :
    termSubstVec L k vector (termBindFreeVecAt L depth k terms) = terms := by
  apply nth_ext' k
  · simp [hb.isUTerm]
  · exact ht.lh
  · intro i hi
    rw [nth_termSubstVec hb.isUTerm hi,nth_termBindFreeVecAt depth ht.isUTerm hi]
    apply termBindFreeAt_inverse (ht.nth hi) slots vector hw
    · simpa [nth_termBindFreeVecAt depth ht.isUTerm hi] using hb.nth hi
    · exact ho

lemma bindFreeAt_inverse {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ slots vector : V, IsSemitermVec L slots depth vector →
      IsSemiformula L slots (bindFreeAt L depth p) → Opening depth slots vector →
      subst L vector (bindFreeAt L depth p) = p := by
  apply IsSemiformula.pi1_structural_induction (P := fun depth p =>
    ∀ slots vector : V, IsSemitermVec L slots depth vector →
      IsSemiformula L slots (bindFreeAt L depth p) → Opening depth slots vector →
      subst L vector (bindFreeAt L depth p) = p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro depth k R terms hR ht slots vector hw hb ho
    have hargs : IsSemitermVec L k slots (termBindFreeVecAt L depth k terms) := by
      have h : L.IsRel k R ∧ IsSemitermVec L k slots (termBindFreeVecAt L depth k terms) := by
        simpa [bindFreeAt_rel depth hR ht.isUTerm] using hb
      exact h.2
    rw [bindFreeAt_rel depth hR ht.isUTerm,substs_rel hR hargs.isUTerm,
      termBindFreeVecAt_inverse ht hw hargs ho]
  · intro depth k R terms hR ht slots vector hw hb ho
    have hargs : IsSemitermVec L k slots (termBindFreeVecAt L depth k terms) := by
      have h : L.IsRel k R ∧ IsSemitermVec L k slots (termBindFreeVecAt L depth k terms) := by
        simpa [bindFreeAt_nrel depth hR ht.isUTerm] using hb
      exact h.2
    rw [bindFreeAt_nrel depth hR ht.isUTerm,substs_nrel hR hargs.isUTerm,
      termBindFreeVecAt_inverse ht hw hargs ho]
  · intro depth slots vector hw hb ho; simp
  · intro depth slots vector hw hb ho; simp
  · intro depth p q hp hq ihp ihq slots vector hw hb ho
    have hparts : IsSemiformula L slots (bindFreeAt L depth p) ∧
        IsSemiformula L slots (bindFreeAt L depth q) := by
      simpa [bindFreeAt_and depth hp.isUFormula hq.isUFormula] using hb
    rw [bindFreeAt_and depth hp.isUFormula hq.isUFormula,
      substs_and (bindFreeAt_isUFormula hp.isUFormula depth) (bindFreeAt_isUFormula hq.isUFormula depth),
      ihp slots vector hw hparts.1 ho,ihq slots vector hw hparts.2 ho]
  · intro depth p q hp hq ihp ihq slots vector hw hb ho
    have hparts : IsSemiformula L slots (bindFreeAt L depth p) ∧
        IsSemiformula L slots (bindFreeAt L depth q) := by
      simpa [bindFreeAt_or depth hp.isUFormula hq.isUFormula] using hb
    rw [bindFreeAt_or depth hp.isUFormula hq.isUFormula,
      substs_or (bindFreeAt_isUFormula hp.isUFormula depth) (bindFreeAt_isUFormula hq.isUFormula depth),
      ihp slots vector hw hparts.1 ho,ihq slots vector hw hparts.2 ho]
  · intro depth p hp ih slots vector hw hb ho
    have hbody : IsSemiformula L (slots+1) (bindFreeAt L (depth+1) p) := by
      simpa [bindFreeAt_all depth hp.isUFormula] using hb
    rw [bindFreeAt_all depth hp.isUFormula,substs_all (bindFreeAt_isUFormula hp.isUFormula (depth+1)),
      ih (slots+1) (qVec L vector) hw.qVec hbody (ho.qVec hw)]
  · intro depth p hp ih slots vector hw hb ho
    have hbody : IsSemiformula L (slots+1) (bindFreeAt L (depth+1) p) := by
      simpa [bindFreeAt_exs depth hp.isUFormula] using hb
    rw [bindFreeAt_exs depth hp.isUFormula,substs_ex (bindFreeAt_isUFormula hp.isUFormula (depth+1)),
      ih (slots+1) (qVec L vector) hw.qVec hbody (ho.qVec hw)]

lemma fvarVec_isTermVec (slots : V) : IsSemitermVec L slots 0 (fvarVec slots) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨len_fvarVec slots,?_⟩
  intro i hi
  rw [nth_fvarVec slots i hi]
  simp

/-- The desired inverse-freeization statement for every internally coded Formula. -/
theorem bindFreeAt_closing {p : V} (hp : IsFormula L p) :
    IsUFormula L (bindFreeAt L 0 p) ∧ shift L (bindFreeAt L 0 p) = bindFreeAt L 0 p ∧
      subst L (fvarVec (bv L (bindFreeAt L 0 p))) (bindFreeAt L 0 p) = p := by
  have hu := bindFreeAt_isUFormula hp.isUFormula (0 : V)
  refine ⟨hu,bindFreeAt_shift_fixed hp.isUFormula 0,?_⟩
  apply bindFreeAt_inverse hp (bv L (bindFreeAt L 0 p)) _ (fvarVec_isTermVec _)
  · exact hu.isSemiformula
  · refine ⟨by simp,by simp,?_⟩
    intro x hx hdx
    simpa using nth_fvarVec (bv L (bindFreeAt L 0 p)) x hx

end LeanProofs.ZFCinPA.ModelCodedBindFree
