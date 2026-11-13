module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherenceSupply
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceInvariant
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqSupportedValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker RelationalSource.Numeric NumericPAeqValueCoherence NumericPAeqSupportedValueTotality
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] supportedValueEnvironmentGraph
noncomputable def supportedCoherenceEnvironmentGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “s b c f g t. !supportedValueEnvironmentGraph s b f t ∧ !supportedValueEnvironmentGraph s c g t”
theorem supportedCoherenceEnvironment_graph (s b c f g t:V):
    supportedCoherenceEnvironmentGraph.val.Evalb ![s,b,c,f,g,t] ↔ SupportedCoherenceEnvironment s b c f g t := by
  simp [supportedCoherenceEnvironmentGraph,SupportedCoherenceEnvironment,supportedValueEnvironment_graph,Matrix.comp_vecCons'']
attribute [local irreducible] coherenceGraph supportedCoherenceEnvironmentGraph coverageGraph
attribute [local irreducible] coherenceCertificateGraph
noncomputable def coherenceInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s b c f g, !supportedCoherenceEnvironmentGraph s b c f g t → ∀ native lo z p,
    !coherenceGraph p s b c f g t → !coverageGraph 0 native lo z p →
    ∃ code, !coherenceCertificateGraph code s b c f g t native lo z”
theorem coherence_invariant (k:V):coherenceInvariant.Evalb ![k] ↔
    ∀t<k,SupportedCoherenceSupply (V:=V) t := by
  simp [coherenceInvariant,SupportedCoherenceSupply,supportedCoherenceEnvironment_graph,coherence_graph,
    coverage_graph,coherenceCertificate_graph,Matrix.comp_vecCons'']
#print axioms supportedCoherenceEnvironment_graph
#print axioms coherence_invariant
end PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherence
