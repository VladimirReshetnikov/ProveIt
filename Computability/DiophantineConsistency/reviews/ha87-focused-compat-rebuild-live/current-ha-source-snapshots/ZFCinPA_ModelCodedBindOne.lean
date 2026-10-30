import ZFCinPA.ModelCodedSpecialization

/-!
Represented binding of one named free variable.
At internal binder depth d, only free label a becomes bound label d;
existing bound labels and every other free label are retained. The fixed
Sigma1 graphs precede the arithmetic model. The opening inverse quantifies
over arbitrary internal labels, depths and well-formed formula codes.
This supplies syntax for a later numeric decoder, not proof transport for GEN.
-/
namespace LeanProofs.ZFCinPA.ModelCodedBindOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace TermBinder

def blueprint : Language.TermRec.Blueprint 2 where
  bvar := .mkSigma “out z chosen depth. !qqBvarDef out z”
  fvar := .mkSigma “out x chosen depth.
    (x = chosen ∧ !qqBvarDef out depth) ∨ (x ≠ chosen ∧ !qqFvarDef out x)”
  func := .mkSigma “out k f oldArgs newArgs chosen depth. !qqFuncDef out k f newArgs”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar _ z := ^#z
  fvar parameters x := by
    classical
    exact if x = parameters 0 then ^#(parameters 1) else ^&x
  func _ k f _ newArgs := ^func k f newArgs
  bvar_defined := .mk fun e => by simp [blueprint]
  fvar_defined := .mk fun e => by
    classical
    by_cases h : e 1 = e 2 <;> simp [blueprint,h]
  func_defined := .mk fun e => by simp [blueprint]

end TermBinder

noncomputable def termBindOneAt (L : Language) [L.Encodable] [L.LORDefinable]
    (chosen depth term : V) : V := TermBinder.construction.result L ![chosen,depth] term
noncomputable def termBindOneVecAt (L : Language) [L.Encodable] [L.LORDefinable]
    (chosen depth arity terms : V) : V :=
  TermBinder.construction.resultVec L ![chosen,depth] arity terms
noncomputable def termBindOneAtDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 4 :=
  (TermBinder.blueprint.result L).rew (Rew.subst ![#0,#3,#1,#2])
noncomputable def termBindOneVecAtDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 5 :=
  (TermBinder.blueprint.resultVec L).rew (Rew.subst ![#0,#3,#4,#1,#2])
instance termBindOneAt_defined :
    𝚺₁-Function₃[V] (termBindOneAt L) via termBindOneAtDef L := .mk fun e => by
  simpa [termBindOneAtDef,termBindOneAt,Matrix.comp_vecCons']
    using (TermBinder.construction.result_defined (L := L)).defined ![e 0,e 3,e 1,e 2]
instance termBindOneVecAt_defined :
    𝚺₁-Function₄[V] (termBindOneVecAt L) via termBindOneVecAtDef L := .mk fun e => by
  simpa [termBindOneVecAtDef,termBindOneVecAt,Matrix.comp_vecCons'',Matrix.comp_vecCons']
    using (TermBinder.construction.resultVec_defined (L := L)).defined ![e 0,e 3,e 4,e 1,e 2]

namespace FormulaBinder

/-- The single changing parameter is the pair (chosen label, binder depth). -/
noncomputable def blueprint (L : Language) [L.Encodable] [L.LORDefinable] :
    UformulaRec1.Blueprint where
  rel := .mkSigma “out state k R terms. ∃ chosen, !pi₁Def chosen state ∧
    ∃ depth, !pi₂Def depth state ∧ ∃ args,
    !(termBindOneVecAtDef L) args chosen depth k terms ∧ !qqRelDef out k R args”
  nrel := .mkSigma “out state k R terms. ∃ chosen, !pi₁Def chosen state ∧
    ∃ depth, !pi₂Def depth state ∧ ∃ args,
    !(termBindOneVecAtDef L) args chosen depth k terms ∧ !qqNRelDef out k R args”
  verum := .mkSigma “out state. !qqVerumDef out”
  falsum := .mkSigma “out state. !qqFalsumDef out”
  and := .mkSigma “out state p q left right. !qqAndDef out left right”
  or := .mkSigma “out state p q left right. !qqOrDef out left right”
  all := .mkSigma “out state p body. !qqAllDef out body”
  exs := .mkSigma “out state p body. !qqExsDef out body”
  allChanges := .mkSigma “next state. ∃ chosen, !pi₁Def chosen state ∧
    ∃ depth, !pi₂Def depth state ∧ !pairDef next chosen (depth+1)”
  exsChanges := .mkSigma “next state. ∃ chosen, !pi₁Def chosen state ∧
    ∃ depth, !pi₂Def depth state ∧ !pairDef next chosen (depth+1)”

noncomputable def construction (L : Language) [L.Encodable] [L.LORDefinable] :
    UformulaRec1.Construction V (blueprint L) where
  rel state k R terms := ^rel k R (termBindOneVecAt L (π₁ state) (π₂ state) k terms)
  nrel state k R terms := ^nrel k R (termBindOneVecAt L (π₁ state) (π₂ state) k terms)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ left right := left ^⋏ right
  or _ _ _ left right := left ^⋎ right
  all _ _ body := ^∀ body
  exs _ _ body := ^∃ body
  allChanges state := ⟪π₁ state,π₂ state+1⟫
  exsChanges state := ⟪π₁ state,π₂ state+1⟫
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

noncomputable def bindOneAt (L : Language) [L.Encodable] [L.LORDefinable]
    (chosen depth formula : V) : V :=
  (FormulaBinder.construction L).result L ⟪chosen,depth⟫ formula
noncomputable def rawBindOneDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 3 := (FormulaBinder.blueprint L).result L
noncomputable def bindOneAtDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 4 := .mkSigma “out chosen depth formula.
      ∃ state, !pairDef state chosen depth ∧ !(rawBindOneDef L) out state formula”
instance bindOneAt_defined :
    𝚺₁-Function₃[V] (bindOneAt L) via bindOneAtDef L := .mk fun e => by
  simpa [bindOneAtDef,rawBindOneDef,bindOneAt]
    using (FormulaBinder.construction L).result_defined.defined ![e 0,⟪e 1,e 2⟫,e 3]
private instance termBindOneAt_delta : 𝚫₁-Function₃[V] (termBindOneAt L) :=
  termBindOneAt_defined.graph_delta.to_definable
private instance termBindOneVecAt_delta : 𝚫₁-Function₄[V] (termBindOneVecAt L) :=
  termBindOneVecAt_defined.graph_delta.to_definable
private instance bindOneAt_delta : 𝚫₁-Function₃[V] (bindOneAt L) :=
  bindOneAt_defined.graph_delta.to_definable

@[simp] lemma termBindOneAt_bvar (chosen depth z : V) :
    termBindOneAt L chosen depth (^#z) = ^#z := by
  simp [termBindOneAt,TermBinder.construction]
lemma termBindOneAt_fvar (chosen depth x : V) :
    termBindOneAt L chosen depth (^&x) = if x = chosen then ^#depth else ^&x := by
  simp [termBindOneAt,TermBinder.construction]
@[simp] lemma termBindOneAt_chosen (chosen depth : V) :
    termBindOneAt L chosen depth (^&chosen) = ^#depth := by
  simp [termBindOneAt_fvar]
lemma termBindOneAt_other (chosen depth x : V) (h : x ≠ chosen) :
    termBindOneAt L chosen depth (^&x) = ^&x := by
  simp [termBindOneAt_fvar,h]
lemma termBindOneAt_func (chosen depth : V) {k f terms : V}
    (hf : L.IsFunc k f) (ht : IsUTermVec L k terms) :
    termBindOneAt L chosen depth (^func k f terms) =
      ^func k f (termBindOneVecAt L chosen depth k terms) := by
  simp [termBindOneAt,termBindOneVecAt,TermBinder.construction,hf,ht]
@[simp] lemma termBindOneVecAt_lh (chosen depth : V) {k terms : V}
    (ht : IsUTermVec L k terms) : len (termBindOneVecAt L chosen depth k terms) = k :=
  TermBinder.construction.resultVec_lh L ![chosen,depth] ht
lemma nth_termBindOneVecAt (chosen depth : V) {k terms i : V}
    (ht : IsUTermVec L k terms) (hi : i < k) :
    (termBindOneVecAt L chosen depth k terms).[i] =
      termBindOneAt L chosen depth terms.[i] :=
  TermBinder.construction.nth_resultVec L ![chosen,depth] ht hi

lemma termBindOneAt_isUTerm (chosen depth : V) {term : V} (ht : IsUTerm L term) :
    IsUTerm L (termBindOneAt L chosen depth term) := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z; simp
  · intro x
    classical
    by_cases h : x = chosen <;> simp [termBindOneAt_fvar,h]
  · intro k f terms hf hv ih
    have hargs : IsUTermVec L k (termBindOneVecAt L chosen depth k terms) := by
      refine ⟨(termBindOneVecAt_lh chosen depth hv).symm,?_⟩
      intro i hi
      rw [nth_termBindOneVecAt chosen depth hv hi]
      exact ih i hi
    rw [termBindOneAt_func chosen depth hf hv]
    exact IsUTerm.func_iff.mpr ⟨hf,hargs⟩
lemma termBindOneVecAt_isUTerm (chosen depth : V) {k terms : V}
    (ht : IsUTermVec L k terms) :
    IsUTermVec L k (termBindOneVecAt L chosen depth k terms) := by
  refine ⟨(termBindOneVecAt_lh chosen depth ht).symm,?_⟩
  intro i hi
  rw [nth_termBindOneVecAt chosen depth ht hi]
  exact termBindOneAt_isUTerm chosen depth (ht.nth hi)

lemma termBindOneAt_isSemiterm {depth term : V} (ht : IsSemiterm L depth term) :
    ∀ chosen : V, IsSemiterm L (depth+1) (termBindOneAt L chosen depth term) := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z hz chosen
    rw [termBindOneAt_bvar]
    simpa using lt_trans hz (show depth < depth+1 by simp)
  · intro x chosen
    classical
    by_cases h : x = chosen <;> simp [termBindOneAt_fvar,h]
  · intro k f terms hf hv ih chosen
    have hargs : IsSemitermVec L k (depth+1) (termBindOneVecAt L chosen depth k terms) := by
      apply IsSemitermVec.iff.mpr
      refine ⟨termBindOneVecAt_lh chosen depth hv.isUTerm,?_⟩
      intro i hi
      rw [nth_termBindOneVecAt chosen depth hv.isUTerm hi]
      exact ih i hi chosen
    rw [termBindOneAt_func chosen depth hf hv.isUTerm]
    exact IsSemiterm.func.mpr ⟨hf,hargs⟩
lemma termBindOneVecAt_isSemiterm {depth k terms : V}
    (ht : IsSemitermVec L k depth terms) (chosen : V) :
    IsSemitermVec L k (depth+1) (termBindOneVecAt L chosen depth k terms) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨termBindOneVecAt_lh chosen depth ht.isUTerm,?_⟩
  intro i hi
  rw [nth_termBindOneVecAt chosen depth ht.isUTerm hi]
  exact termBindOneAt_isSemiterm (ht.nth hi) chosen

lemma bindOneAt_rel (chosen depth : V) {k R terms : V}
    (hR : L.IsRel k R) (ht : IsUTermVec L k terms) :
    bindOneAt L chosen depth (^rel k R terms) =
      ^rel k R (termBindOneVecAt L chosen depth k terms) := by
  simp [bindOneAt,FormulaBinder.construction,hR,ht]
lemma bindOneAt_nrel (chosen depth : V) {k R terms : V}
    (hR : L.IsRel k R) (ht : IsUTermVec L k terms) :
    bindOneAt L chosen depth (^nrel k R terms) =
      ^nrel k R (termBindOneVecAt L chosen depth k terms) := by
  simp [bindOneAt,FormulaBinder.construction,hR,ht]
@[simp] lemma bindOneAt_verum (chosen depth : V) : bindOneAt L chosen depth ^⊤ = ^⊤ := by
  simp [bindOneAt,FormulaBinder.construction]
@[simp] lemma bindOneAt_falsum (chosen depth : V) : bindOneAt L chosen depth ^⊥ = ^⊥ := by
  simp [bindOneAt,FormulaBinder.construction]
lemma bindOneAt_and (chosen depth : V) {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bindOneAt L chosen depth (p ^⋏ q) =
      bindOneAt L chosen depth p ^⋏ bindOneAt L chosen depth q := by
  simp [bindOneAt,FormulaBinder.construction,hp,hq]
lemma bindOneAt_or (chosen depth : V) {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bindOneAt L chosen depth (p ^⋎ q) =
      bindOneAt L chosen depth p ^⋎ bindOneAt L chosen depth q := by
  simp [bindOneAt,FormulaBinder.construction,hp,hq]
lemma bindOneAt_all (chosen depth : V) {p : V} (hp : IsUFormula L p) :
    bindOneAt L chosen depth (^∀ p) = ^∀ (bindOneAt L chosen (depth+1) p) := by
  simp [bindOneAt,FormulaBinder.construction,hp]
lemma bindOneAt_exs (chosen depth : V) {p : V} (hp : IsUFormula L p) :
    bindOneAt L chosen depth (^∃ p) = ^∃ (bindOneAt L chosen (depth+1) p) := by
  simp [bindOneAt,FormulaBinder.construction,hp]

lemma bindOneAt_isSemiformula {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ chosen : V, IsSemiformula L (depth+1) (bindOneAt L chosen depth p) := by
  apply IsSemiformula.pi1_structural_induction (P := fun depth p =>
    ∀ chosen : V, IsSemiformula L (depth+1) (bindOneAt L chosen depth p))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  all_goals
    intros
    simp (discharger := aesop (add safe [IsSemitermVec.isUTerm, IsSemiformula.isUFormula]))
      [*, bindOneAt_rel, bindOneAt_nrel, termBindOneVecAt_isSemiterm,
        bindOneAt_and, bindOneAt_or, bindOneAt_all, bindOneAt_exs,
        IsSemiformula.rel, IsSemiformula.nrel, IsSemiformula.and, IsSemiformula.or]

lemma termBindOneAt_inverse {depth term : V} (ht : IsSemiterm L depth term) :
    ∀ chosen : V,
    termSubst L (qVecIter L depth (^&chosen ∷ 0))
      (termBindOneAt L chosen depth term) = term := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z hz chosen
    rw [termBindOneAt_bvar,termSubst_bvar]
    exact (qVecIter_free_spec depth chosen).1 z hz
  · intro x chosen
    classical
    by_cases h : x = chosen
    · rw [h,termBindOneAt_chosen,termSubst_bvar]
      exact (qVecIter_free_spec depth chosen).2
    · rw [termBindOneAt_other chosen depth x h,termSubst_fvar]
  · intro k f terms hf hv ih chosen
    rw [termBindOneAt_func chosen depth hf hv.isUTerm,
      termSubst_func hf (termBindOneVecAt_isUTerm chosen depth hv.isUTerm)]
    apply congrArg (fun args => ^func k f args)
    apply nth_ext' k
    · simp [termBindOneVecAt_isUTerm chosen depth hv.isUTerm]
    · exact hv.lh
    · intro i hi
      rw [nth_termSubstVec (termBindOneVecAt_isUTerm chosen depth hv.isUTerm) hi,
        nth_termBindOneVecAt chosen depth hv.isUTerm hi]
      exact ih i hi chosen
lemma termBindOneVecAt_inverse {depth k terms : V}
    (ht : IsSemitermVec L k depth terms) (chosen : V) :
    termSubstVec L k (qVecIter L depth (^&chosen ∷ 0))
      (termBindOneVecAt L chosen depth k terms) = terms := by
  apply nth_ext' k
  · simp [termBindOneVecAt_isUTerm chosen depth ht.isUTerm]
  · exact ht.lh
  · intro i hi
    rw [nth_termSubstVec (termBindOneVecAt_isUTerm chosen depth ht.isUTerm) hi,
      nth_termBindOneVecAt chosen depth ht.isUTerm hi]
    exact termBindOneAt_inverse (ht.nth hi) chosen

/-- Reopening the newly bound slot recovers the exact input, at every internal depth. -/
theorem bindOneAt_inverse {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ chosen : V,
    subst L (qVecIter L depth (^&chosen ∷ 0)) (bindOneAt L chosen depth p) = p := by
  apply IsSemiformula.pi1_structural_induction (P := fun depth p =>
    ∀ chosen : V,
    subst L (qVecIter L depth (^&chosen ∷ 0)) (bindOneAt L chosen depth p) = p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  all_goals
    intros
    simp (discharger := aesop (add safe [IsSemiformula.isUFormula, IsSemitermVec.isUTerm,
      bindOneAt_isSemiformula, termBindOneVecAt_isUTerm]))
      [*, bindOneAt_rel, bindOneAt_nrel, bindOneAt_and, bindOneAt_or, bindOneAt_all, bindOneAt_exs,
        substs_rel, substs_nrel, substs_and, substs_or, substs_all, substs_ex,
        termBindOneVecAt_inverse, ← qVecIter_succ]

/-- Syntax for a future decoder's named universal binder; not a GEN proof rule. -/
noncomputable def namedAll (L : Language) [L.Encodable] [L.LORDefinable]
    (chosen formula : V) : V := ^∀ (bindOneAt L chosen 0 formula)
noncomputable def namedAllDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 3 := .mkSigma “out chosen formula.
      ∃ body, !(bindOneAtDef L) body chosen 0 formula ∧ !qqAllDef out body”
instance namedAll_defined : 𝚺₁-Function₂[V] (namedAll L) via namedAllDef L :=
  .mk fun e => by simp [namedAllDef,namedAll]
theorem namedAll_isFormula {p : V} (hp : IsFormula L p) (chosen : V) :
    IsFormula L (namedAll L chosen p) := by
  simpa [namedAll] using bindOneAt_isSemiformula hp chosen

theorem bindOneAt_open {p : V} (hp : IsFormula L p) (chosen : V) :
    substs1 L (^&chosen) (bindOneAt L chosen 0 p) = p := by
  simpa [substs1] using bindOneAt_inverse hp chosen

end LeanProofs.ZFCinPA.ModelCodedBindOne
