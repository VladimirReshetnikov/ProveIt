module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTargetSubst
@[expose] public section

/-! Existential value-output syntax. This defines a formula, not a proof of
semantic totality. Bound and free environments contain target term codes. -/
namespace M6.PA.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def valueTotalityCode (b f t : V) : V :=
  qqExs (valueSyntax (parameters (shiftTerms b) (shiftTerms f) (qqBvar 0)) t)
attribute [local irreducible] valueSyntaxGraph shiftTermsGraph parametersGraph
noncomputable def valueTotalityGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out b f t. ∃ bs fs z param body,
    !shiftTermsGraph bs b ∧ !shiftTermsGraph fs f ∧ !qqBvarDef z 0 ∧
    !parametersGraph param bs fs z ∧ !valueSyntaxGraph body param t ∧ !qqExsDef out body”
theorem valueTotality_graph (out b f t : V) :
    valueTotalityGraph.val.Evalb ![out,b,f,t] ↔ out=valueTotalityCode b f t := by
  simp [valueTotalityGraph,valueTotalityCode,shiftTerms_graph,parameters_graph,valueSyntax_graph,Matrix.comp_vecCons'']
theorem valueTotality_total_unique (b f t : V) :
    ∃! out,valueTotalityGraph.val.Evalb ![out,b,f,t] := by
  refine ⟨valueTotalityCode b f t,(valueTotality_graph _ _ _ _).mpr rfl,?_⟩
  intro out h; exact (valueTotality_graph _ _ _ _).mp h

theorem valueTotality_isSemiformula {s n b f t : V}
    (hb:IsSemitermVec language s n b) (hf:IsSemitermVec language (len f) n f)
    (ht:IsSemiterm Presentation.language s t) (hbound:t≤len f) :
    IsSemiformula language n (valueTotalityCode b f t) := by
  apply IsSemiformula.exs.mpr
  apply valueSyntax_isSemiformula
  refine ⟨?_,ht,?_⟩
  · simp only [ParametersValid,parameters_bound,parameters_free,parameters_result]
    refine ⟨shiftTerms_isSemitermVec hb,?_,by simp⟩
    rw [shiftTerms_length hf]
    exact shiftTerms_isSemitermVec hf
  · simpa only [parameters_free,shiftTerms_length hf] using hbound

#print axioms valueTotality_graph
#print axioms valueTotality_total_unique
#print axioms valueTotality_isSemiformula
end M6.PA.NumericPAeqValueTotality

