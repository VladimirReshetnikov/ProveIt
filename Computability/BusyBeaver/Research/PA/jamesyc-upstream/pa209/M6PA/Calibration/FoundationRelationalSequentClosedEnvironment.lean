module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentShift
@[expose] public section

/-! Independence from arbitrary finite free-label environments under the
explicit coded shift-fixed condition. No semantic closedness equivalence is
claimed, and bound environments remain unchanged. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

attribute [local irreducible] parametersGraph translateGraph shiftGraph
noncomputable def closedEnvironmentGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “p b f lo z. ∃ param empty out, !parametersGraph param b f lo z ∧
    !parametersGraph empty b 0 lo z ∧ !translateGraph out param p ∧ !translateGraph out empty p”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem closedEnvironment_graph (p b f lo z : V) :
    closedEnvironmentGraph.val.Evalb ![p,b,f,lo,z] ↔
    translate (parameters b f lo z) p=translate (parameters b 0 lo z) p := by
  simp [closedEnvironmentGraph,parameters_graph,translate_graph,Matrix.comp_vecCons'',eq_comm]

attribute [local irreducible] closedEnvironmentGraph
noncomputable def closedEnvironmentInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ p b f lo z, !((isUFormula language).sigma) p → !(shiftGraph language) p p →
    (∃ length, !lenDef length f ∧ length≤n) → !closedEnvironmentGraph p b f lo z”

theorem closedEnvironment_invariant (n : V) : closedEnvironmentInvariant.Evalb ![n] ↔
    ∀ p b f lo z : V, IsUFormula language p → Bootstrapping.shift language p=p →
      len f≤n → translate (parameters b f lo z) p=translate (parameters b 0 lo z) p := by
  simp [closedEnvironmentInvariant,closedEnvironment_graph,Matrix.comp_vecCons'',eq_comm]

variable [V↓[ℒₒᵣ] ⊧* theory]

theorem translate_closed_free_environment (p b f lo z : V)
    (hp : IsUFormula language p) (hc : Bootstrapping.shift language p=p) :
    translate (parameters b f lo z) p=translate (parameters b 0 lo z) p := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ p b f lo z : V, IsUFormula language p →
      Bootstrapping.shift language p=p → len f≤n →
      translate (parameters b f lo z) p=translate (parameters b 0 lo z) p := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ p b f lo z : V, IsUFormula language p → Bootstrapping.shift language p=p →
        len f≤n → translate (parameters b f lo z) p=translate (parameters b 0 lo z) p) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb closedEnvironmentInvariant,by trivial,?_⟩
      intro n
      simpa using (closedEnvironment_invariant (V:=V) n).symm
    · intro p b f lo z hp hc hf
      have he : f=0 := by simpa using hf
      simp [he]
    · intro n ih p b f lo z hp hc hf
      rcases nil_or_adjoin f with rfl | ⟨x,tail,rfl⟩
      · rfl
      · have ht : len tail≤n := by simpa using hf
        have he := translate_shift p (parameters b tail lo z) x hp
        rw [hc,prependFree_parameters] at he
        exact he.trans (ih p b tail lo z hp hc ht)
  exact hall (len f) p b f lo z hp hc le_rfl

theorem translate_closed_free_environments (p b f g lo z : V)
    (hp : IsUFormula language p) (hc : Bootstrapping.shift language p=p) :
    translate (parameters b f lo z) p=translate (parameters b g lo z) p :=
  (translate_closed_free_environment p b f lo z hp hc).trans
    (translate_closed_free_environment p b g lo z hp hc).symm

noncomputable def closedEnvironmentSentence : ArithmeticSentence :=
  “∀ p b f lo z, !((isUFormula language).sigma) p → !(shiftGraph language) p p →
    !closedEnvironmentGraph p b f lo z”

theorem pa_proves_closedEnvironment : theory ⊢ closedEnvironmentSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [closedEnvironmentSentence,models_iff,closedEnvironment_graph,Matrix.comp_vecCons'',eq_comm]
  intro p b f lo z hp hc
  exact translate_closed_free_environment p b f lo z hp hc.symm

#print axioms closedEnvironment_graph
#print axioms closedEnvironment_invariant
#print axioms translate_closed_free_environment
#print axioms translate_closed_free_environments
#print axioms pa_proves_closedEnvironment
end M6.PA.RelationalSource.Numeric

