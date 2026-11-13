module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaRealizationSyntax
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationGraphs
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqValueVectorRealization
open NumericPAeqSupportedVectorRealization (vectorInputGraph vectorInput_graph)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] freeSupportedGraph NumericPAeqTerm.freeSupportedGraph parametersGraph formulaSyntaxGraph vectorInputGraph
noncomputable def formulaEnvironmentGraph : 𝚺ᴬ₁.Semisentence 7 := .mkSigma
  “s r b f a w p. ∃ l, !lenDef l f ∧
    !((isSemitermVec RelationalSource.language).sigma) r 0 b ∧
    !((isSemitermVec RelationalSource.language).sigma) l 0 f ∧
    !((isSemitermVec RelationalSource.language).sigma) s 0 a ∧
    !((isSemiformula Presentation.language).sigma) s p ∧
    !((isSemitermVec Presentation.language).sigma) s r w ∧ !freeSupportedGraph l p ∧
    ∀ i<s, ∃ v, !nthDef v w i ∧ !NumericPAeqTerm.freeSupportedGraph l v”
theorem formulaEnvironment_graph (s r b f a w p:V):
    formulaEnvironmentGraph.val.Evalb ![s,r,b,f,a,w,p] ↔ FormulaEnvironment s r b f a w p := by
  simp [formulaEnvironmentGraph,FormulaEnvironment,freeSupported_graph,NumericPAeqTerm.freeSupported_graph,Matrix.comp_vecCons'']
noncomputable def formulaComparisonGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “out b f a w p. ∃ v bp ap left right forward backward,
    !(substsGraph Presentation.language) v w p ∧ !parametersGraph bp b f ∧ !parametersGraph ap a f ∧
    !formulaSyntaxGraph left bp v ∧ !formulaSyntaxGraph right ap p ∧
    !(impGraph RelationalSource.language) forward left right ∧
    !(impGraph RelationalSource.language) backward right left ∧ !qqAndDef out forward backward”
theorem formulaComparison_graph (out b f a w p:V):
    formulaComparisonGraph.val.Evalb ![out,b,f,a,w,p] ↔ out=formulaComparison b f a w p := by
  simp [formulaComparisonGraph,formulaComparison,substitutedFormula,originalFormula,parameters_graph,
    formulaSyntax_graph,Matrix.comp_vecCons'']
attribute [local irreducible] formulaComparisonGraph
noncomputable def formulaGraph : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
  “out s r b f a w p. ∃ ant con, !vectorInputGraph ant s r b f a w ∧
    !formulaComparisonGraph con b f a w p ∧ !(impGraph RelationalSource.language) out ant con”
theorem formula_graph (out s r b f a w p:V):
    formulaGraph.val.Evalb ![out,s,r,b,f,a,w,p] ↔ out=formulaCode s r b f a w p := by
  simp [formulaGraph,formulaCode,vectorInput_graph,formulaComparison_graph,Matrix.comp_vecCons'']
#print axioms formulaEnvironment_graph
#print axioms formulaComparison_graph
#print axioms formula_graph
end PA196.Arithmetic.Transport.NumericPAeqFormulaRealization

