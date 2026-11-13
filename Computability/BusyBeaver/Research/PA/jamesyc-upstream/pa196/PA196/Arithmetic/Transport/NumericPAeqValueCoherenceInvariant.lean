module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceSupply
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] coherenceGraph coherenceEnvironmentGraph coverageGraph parametersGraph translateGraph verifyGraph
noncomputable def coherenceCertificateGraph : 𝚺ᴬ₁.Semisentence 10 := .mkSigma
  “code s b c f g t native lo z. ∃ p param out, !coherenceGraph p s b c f g t ∧
    !parametersGraph param 0 native lo z ∧ !translateGraph out param p ∧ !verifyGraph (out+1) code”
theorem coherenceCertificate_graph (code s b c f g t native lo z:V):
    coherenceCertificateGraph.val.Evalb ![code,s,b,c,f,g,t,native,lo,z] ↔
      verifyValue code=translate (parameters 0 native lo z) (coherenceCode s b c f g t)+1 := by
  simp [coherenceCertificateGraph,coherence_graph,parameters_graph,translate_graph,verify_graph,eq_comm,Matrix.comp_vecCons'']
attribute [local irreducible] coherenceCertificateGraph
noncomputable def coherenceInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s b c f g, !coherenceEnvironmentGraph s b c f g t → ∀ native lo z p,
    !coherenceGraph p s b c f g t → !coverageGraph 0 native lo z p →
    ∃ code, !coherenceCertificateGraph code s b c f g t native lo z”
theorem coherence_invariant (k:V):coherenceInvariant.Evalb ![k] ↔
    ∀t<k,CoherenceSupply (V:=V) t := by
  simp [coherenceInvariant,CoherenceSupply,coherenceEnvironment_graph,coherence_graph,
    coverage_graph,coherenceCertificate_graph,Matrix.comp_vecCons'']
#print axioms coherenceCertificate_graph
#print axioms coherence_invariant
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
