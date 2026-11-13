module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationSyntax
public import PA196.Arithmetic.Transport.NumericPAeqCoherencePairwiseGraph
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence NumericPAeqValueVectorRealization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] freeSupportedGraph parametersGraph valueSyntaxGraph pairwiseCodeGraph
  NumericPAeqValueDomainGuard.guardGraph NumericPAeqValueRealizationGuard.guardGraph
noncomputable def vectorEnvironmentGraph : 𝚺ᴬ₁.Semisentence 7 := .mkSigma
  “s r b f a w t. ∃ l, !lenDef l f ∧
    !((isSemitermVec RelationalSource.language).sigma) r 0 b ∧
    !((isSemitermVec RelationalSource.language).sigma) l 0 f ∧
    !((isSemitermVec RelationalSource.language).sigma) s 0 a ∧
    !((isSemiterm Presentation.language).sigma) s t ∧
    !((isSemitermVec Presentation.language).sigma) s r w ∧ !freeSupportedGraph l t ∧
    ∀ i<s, ∃ v, !nthDef v w i ∧ !freeSupportedGraph l v”
theorem vectorEnvironment_graph (s r b f a w t:V):
    vectorEnvironmentGraph.val.Evalb ![s,r,b,f,a,w,t] ↔ SupportedVectorEnvironment s r b f a w t := by
  simp [vectorEnvironmentGraph,SupportedVectorEnvironment,freeSupported_graph,Matrix.comp_vecCons'']
noncomputable def vectorInputGraph : 𝚺ᴬ₁.Semisentence 7 := .mkSigma
  “out s r b f a w. ∃ l db df da left right values tail,
    !lenDef l f ∧ !NumericPAeqValueDomainGuard.guardGraph db b r ∧
    !NumericPAeqValueDomainGuard.guardGraph df f l ∧ !NumericPAeqValueDomainGuard.guardGraph da a s ∧
    !qqAndDef left db df ∧ !qqAndDef right da df ∧
    !NumericPAeqValueRealizationGuard.guardGraph values b f w a s ∧ !qqAndDef tail right values ∧
    !qqAndDef out left tail”
theorem vectorInput_graph (out s r b f a w:V):
    vectorInputGraph.val.Evalb ![out,s,r,b,f,a,w] ↔ out=vectorInput s r b f a w := by
  simp [vectorInputGraph,vectorInput,inputDomain,NumericPAeqValueDomainGuard.guard_graph,
    NumericPAeqValueRealizationGuard.guard_graph,Matrix.comp_vecCons'']
noncomputable def vectorComparisonGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “out b f a w t. ∃ v x bp ap p q, !(termSubstGraph Presentation.language) v w t ∧
    !qqBvarDef x 0 ∧ !parametersGraph bp b f x ∧ !parametersGraph ap a f x ∧
    !valueSyntaxGraph p bp v ∧ !valueSyntaxGraph q ap t ∧ !pairwiseCodeGraph out p q”
theorem vectorComparison_graph (out b f a w t:V):
    vectorComparisonGraph.val.Evalb ![out,b,f,a,w,t] ↔ out=vectorComparison b f a w t := by
  simp [vectorComparisonGraph,vectorComparison,valuePredicate,parameters_graph,valueSyntax_graph,
    pairwiseCode_graph,Matrix.comp_vecCons'']
attribute [local irreducible] vectorInputGraph vectorComparisonGraph
noncomputable def vectorGraph : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
  “out s r b f a w t. ∃ ant con, !vectorInputGraph ant s r b f a w ∧
    !vectorComparisonGraph con b f a w t ∧ !(impGraph RelationalSource.language) out ant con”
theorem vector_graph (out s r b f a w t:V):
    vectorGraph.val.Evalb ![out,s,r,b,f,a,w,t] ↔ out=vectorCode s r b f a w t := by
  simp [vectorGraph,vectorCode,vectorInput_graph,vectorComparison_graph,Matrix.comp_vecCons'']
#print axioms vectorEnvironment_graph
#print axioms vectorInput_graph
#print axioms vectorComparison_graph
#print axioms vector_graph
end PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization

