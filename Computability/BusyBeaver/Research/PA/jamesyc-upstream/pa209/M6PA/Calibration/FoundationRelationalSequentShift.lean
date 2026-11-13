module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentShiftLabels
@[expose] public section

/-! Exact formula-shift compatibility by full-PA source-code induction.
The parameter extension and common reserve are literal, not alpha conversion. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

attribute [local irreducible] prependFreeGraph translateGraph shiftGraph
noncomputable def shiftAgreementGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “param p x. ∃ sp ext out, !(shiftGraph language) sp p ∧
    !prependFreeGraph ext x param ∧ !translateGraph out ext sp ∧ !translateGraph out param p”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shiftAgreement_graph (param p x : V) :
    shiftAgreementGraph.val.Evalb ![param,p,x] ↔
      translate (prependFree x param) (Bootstrapping.shift language p)=translate param p := by
  simp [shiftAgreementGraph,prependFree_graph,translate_graph,Matrix.comp_vecCons'',eq_comm]

attribute [local irreducible] shiftAgreementGraph
noncomputable def shiftAgreementInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ p<n, !((isUFormula language).sigma) p → ∀ param x, !shiftAgreementGraph param p x”

theorem shiftAgreement_invariant (n : V) : shiftAgreementInvariant.Evalb ![n] ↔
    ∀ p<n, IsUFormula language p → ∀ param x,
      translate (prependFree x param) (Bootstrapping.shift language p)=translate param p := by
  simp [shiftAgreementInvariant,shiftAgreement_graph,Matrix.comp_vecCons'']

attribute [local irreducible] translate shiftAgreementInvariant
variable [V↓[ℒₒᵣ] ⊧* theory]

private theorem shift_source_step (p : V) (hvalid : IsUFormula language p)
    (ih : ∀ q<p, IsUFormula language q → ∀ param x,
      translate (prependFree x param) (Bootstrapping.shift language q)=translate param q) :
    ∀ param x, translate (prependFree x param) (Bootstrapping.shift language p)=translate param p := by
  intro param x
  rcases IsUFormula.case_iff.mp hvalid with
    ⟨k,r,ts,hr,ht,rfl⟩ | ⟨k,r,ts,hr,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · rw [Bootstrapping.shift_rel hr ht,translate_rel _ _ _ _ hr ht.termShiftVec,
      translate_rel _ _ _ _ hr ht]
    exact totalAtom_termShiftVec param k r ts x ((source_relations _ _).mp hr).1 ht
  · rw [Bootstrapping.shift_nrel hr ht,translate_nrel _ _ _ _ hr ht.termShiftVec,
      translate_nrel _ _ _ _ hr ht,
      totalAtom_termShiftVec param k r ts x ((source_relations _ _).mp hr).1 ht]
  · rw [Bootstrapping.shift_verum,translate_verum,translate_verum]
  · rw [Bootstrapping.shift_falsum,translate_falsum,translate_falsum]
  · rw [Bootstrapping.shift_and hp hq,translate_and _ _ _ hp.shift hq.shift,
      translate_and _ _ _ hp hq,ih p (lt_K!_left p q) hp param x,
      ih q (lt_K!_right p q) hq param x]
  · rw [Bootstrapping.shift_or hp hq,translate_or _ _ _ hp.shift hq.shift,
      translate_or _ _ _ hp hq,ih p (lt_or_left p q) hp param x,
      ih q (lt_or_right p q) hq param x]
  · rw [Bootstrapping.shift_all hp,translate_all _ _ hp.shift,translate_all _ _ hp,
      ← prependFree_advance,ih p (lt_forall p) hp (advance param) x]
    simp [prependFree]
  · rw [Bootstrapping.shift_exs hp,translate_exs _ _ hp.shift,translate_exs _ _ hp,
      ← prependFree_advance,ih p (lt_exists p) hp (advance param) x]
    simp [prependFree]

/-- Source and parameter codes may be nonstandard. The explicit unrestricted
arithmetic invariant supplies full-PA induction, not ordinary Nat induction. -/
theorem translate_shift (p param x : V) (hp : IsUFormula language p) :
    translate (prependFree x param) (Bootstrapping.shift language p)=translate param p := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ p<n, IsUFormula language p → ∀ param x,
      translate (prependFree x param) (Bootstrapping.shift language p)=translate param p := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ p<n, IsUFormula language p → ∀ param x,
        translate (prependFree x param) (Bootstrapping.shift language p)=translate param p) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb shiftAgreementInvariant,by trivial,?_⟩
      intro n
      simpa using (shiftAgreement_invariant (V:=V) n).symm
    · intro p hp
      exact False.elim (by simpa using hp)
    · intro n ih p hp hvalid param x
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he | hlt
      · subst p
        exact shift_source_step n hvalid ih param x
      · exact ih p hlt hvalid param x
  exact hall (p+1) p (lt_add_one p) hp param x

noncomputable def shiftAgreementSentence : ArithmeticSentence :=
  “∀ p param x, !((isUFormula language).sigma) p → !shiftAgreementGraph param p x”

theorem pa_proves_shiftAgreement : theory ⊢ shiftAgreementSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [shiftAgreementSentence,models_iff,shiftAgreement_graph,Matrix.comp_vecCons'']
  intro p param x hp
  exact translate_shift p param x hp

#print axioms shiftAgreement_graph
#print axioms shiftAgreement_invariant
#print axioms shift_source_step
#print axioms translate_shift
#print axioms pa_proves_shiftAgreement
end M6.PA.RelationalSource.Numeric

