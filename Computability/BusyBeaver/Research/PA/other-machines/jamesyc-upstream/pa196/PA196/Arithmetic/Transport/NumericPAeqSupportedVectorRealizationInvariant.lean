module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationSupply
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationGraphs
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqValueVectorRealization PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] vectorGraph vectorEnvironmentGraph coverageGraph parametersGraph translateGraph verifyGraph
noncomputable def vectorCertificateGraph : 𝚺ᴬ₁.Semisentence 11 := .mkSigma
  “code s r b f a w t native lo z. ∃ p param out, !vectorGraph p s r b f a w t ∧
    !parametersGraph param 0 native lo z ∧ !translateGraph out param p ∧ !verifyGraph (out+1) code”
theorem vectorCertificate_graph (code s r b f a w t native lo z:V):
    vectorCertificateGraph.val.Evalb ![code,s,r,b,f,a,w,t,native,lo,z] ↔
      verifyValue code=translate (parameters 0 native lo z) (vectorCode s r b f a w t)+1 := by
  simp [vectorCertificateGraph,vector_graph,parameters_graph,translate_graph,verify_graph,eq_comm,Matrix.comp_vecCons'']
attribute [local irreducible] vectorCertificateGraph
noncomputable def vectorInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s r b f a w, !vectorEnvironmentGraph s r b f a w t → ∀ native lo z p,
    !vectorGraph p s r b f a w t → !coverageGraph 0 native lo z p →
    ∃ code, !vectorCertificateGraph code s r b f a w t native lo z”
theorem vector_invariant (k:V):vectorInvariant.Evalb ![k] ↔
    ∀t<k,VectorSupply (V:=V) t := by
  simp [vectorInvariant,VectorSupply,vectorEnvironment_graph,vector_graph,
    coverage_graph,vectorCertificate_graph,Matrix.comp_vecCons'']
#print axioms vectorCertificate_graph
#print axioms vector_invariant
end PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
