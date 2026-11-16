module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueCoherenceSyntax
@[expose] public section
namespace M6.PA.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] valueEnvironmentGraph valueSyntaxGraph parametersGraph
  NumericPAeqValueDomainGuard.guardGraph NumericPAeqValueIsoGuard.guardGraph templateTwoGraph
noncomputable def coherenceEnvironmentGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “s b c f g t. !valueEnvironmentGraph s b f t ∧ !valueEnvironmentGraph s c g t”
theorem coherenceEnvironment_graph (s b c f g t:V) :
    coherenceEnvironmentGraph.val.Evalb ![s,b,c,f,g,t] ↔ CoherenceEnvironment s b c f g t := by
  simp [coherenceEnvironmentGraph,CoherenceEnvironment,valueEnvironment_graph,Matrix.comp_vecCons'']
noncomputable def comparisonGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “out b c f g t. ∃ x y p q left right pair iso body inner,
    !qqBvarDef x 1 ∧ !qqBvarDef y 0 ∧ !parametersGraph p b f x ∧ !parametersGraph q c g y ∧
    !valueSyntaxGraph left p t ∧ !valueSyntaxGraph right q t ∧ !qqAndDef pair left right ∧
    !NumericPAeqValueIsoGuard.isoCodeGraph iso x y ∧ !(impGraph RelationalSource.language) body pair iso ∧
    !qqAllDef inner body ∧ !qqAllDef out inner”
theorem comparison_graph (out b c f g t:V) :
    comparisonGraph.val.Evalb ![out,b,c,f,g,t] ↔ out=comparisonCode b c f g t := by
  simp [comparisonGraph,comparisonCode,parameters_graph,valueSyntax_graph,
    NumericPAeqValueIsoGuard.isoCode_graph,NumericPAeqValueIsoGuard.isoCode,Matrix.comp_vecCons'']
noncomputable def coherenceInputGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “out s b c f g. ∃ k l m db dc df dg left right ib ifree pair tail,
    !lenDef k f ∧ !lenDef l g ∧ (m≤k ∧ m≤l ∧ (m=k ∨ m=l)) ∧
    !NumericPAeqValueDomainGuard.guardGraph db b s ∧ !NumericPAeqValueDomainGuard.guardGraph df f k ∧
    !NumericPAeqValueDomainGuard.guardGraph dc c s ∧ !NumericPAeqValueDomainGuard.guardGraph dg g l ∧
    !qqAndDef left db df ∧ !qqAndDef right dc dg ∧
    !NumericPAeqValueIsoGuard.guardGraph ib b c s ∧ !NumericPAeqValueIsoGuard.guardGraph ifree f g m ∧
    !qqAndDef pair ib ifree ∧ !qqAndDef tail right pair ∧ !qqAndDef out left tail”
theorem coherenceInput_graph (out s b c f g:V) :
    coherenceInputGraph.val.Evalb ![out,s,b,c,f,g] ↔ out=coherenceInput s b c f g := by
  have hm (m k l:V) : (m≤k ∧ m≤l ∧ (m=k∨m=l)) ↔ m=min k l := by
    constructor
    · rintro ⟨hk,hl,rfl|rfl⟩
      · exact (min_eq_left hl).symm
      · exact (min_eq_right hk).symm
    · rintro rfl
      exact ⟨min_le_left _ _,min_le_right _ _,by rcases le_total k l with h|h; simp [min_eq_left h]; simp [min_eq_right h]⟩
  simp [coherenceInputGraph,coherenceInput,inputDomain,NumericPAeqValueDomainGuard.guard_graph,
    NumericPAeqValueIsoGuard.guard_graph,Matrix.comp_vecCons'',hm]
attribute [local irreducible] comparisonGraph coherenceInputGraph
noncomputable def coherenceGraph : 𝚺ᴬ₁.Semisentence 7 := .mkSigma
  “out s b c f g t. ∃ a q, !coherenceInputGraph a s b c f g ∧ !comparisonGraph q b c f g t ∧
    !(impGraph RelationalSource.language) out a q”
theorem coherence_graph (out s b c f g t:V) :
    coherenceGraph.val.Evalb ![out,s,b,c,f,g,t] ↔ out=coherenceCode s b c f g t := by
  simp [coherenceGraph,coherenceCode,coherenceInput_graph,comparison_graph,Matrix.comp_vecCons'']
#print axioms coherenceEnvironment_graph
#print axioms comparison_graph
#print axioms coherenceInput_graph
#print axioms coherence_graph
end M6.PA.NumericPAeqValueCoherence

