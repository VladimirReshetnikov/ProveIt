module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaRealizationConnectives
public import PA196.Arithmetic.Transport.NumericPAeqFormulaRealizationGraphs
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqValueVectorRealization PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] formulaGraph formulaEnvironmentGraph coverageGraph parametersGraph translateGraph verifyGraph
noncomputable def formulaCertificateGraph : 𝚺ᴬ₁.Semisentence 11 := .mkSigma
  “code s r b f a w t native lo z. ∃ p param out, !formulaGraph p s r b f a w t ∧
    !parametersGraph param 0 native lo z ∧ !translateGraph out param p ∧ !verifyGraph (out+1) code”
theorem formulaCertificate_graph (code s r b f a w t native lo z:V):
    formulaCertificateGraph.val.Evalb ![code,s,r,b,f,a,w,t,native,lo,z] ↔
      verifyValue code=translate (parameters 0 native lo z) (formulaCode s r b f a w t)+1 := by
  simp [formulaCertificateGraph,formula_graph,parameters_graph,translate_graph,verify_graph,eq_comm,Matrix.comp_vecCons'']
attribute [local irreducible] formulaCertificateGraph
noncomputable def formulaInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s r b f a w, !formulaEnvironmentGraph s r b f a w t → ∀ native lo z p,
    !formulaGraph p s r b f a w t → !coverageGraph 0 native lo z p →
    ∃ code, !formulaCertificateGraph code s r b f a w t native lo z”
theorem formula_invariant (k:V):formulaInvariant.Evalb ![k] ↔
    ∀t<k,FormulaSupply (V:=V) t := by
  simp [formulaInvariant,FormulaSupply,formulaEnvironment_graph,formula_graph,
    coverage_graph,formulaCertificate_graph,Matrix.comp_vecCons'']
#print axioms formulaCertificate_graph
#print axioms formula_invariant
end PA196.Arithmetic.Transport.NumericPAeqFormulaRealization

