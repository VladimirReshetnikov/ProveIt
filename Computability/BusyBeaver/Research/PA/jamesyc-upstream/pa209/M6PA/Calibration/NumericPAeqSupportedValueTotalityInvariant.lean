module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueTotalitySteps
@[expose] public section
namespace M6.PA.NumericPAeqSupportedValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint RelationalSource.Numeric NumericPAeqValueTotality
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] guardedTotalityGraph supportedValueEnvironmentGraph coverageGraph parametersGraph translateGraph verifyGraph
noncomputable def totalityCertificateGraph : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
  “code s b f t g lo z. ∃ p param out, !guardedTotalityGraph p s b f t ∧
    !parametersGraph param 0 g lo z ∧ !translateGraph out param p ∧ !verifyGraph (out+1) code”
theorem totalityCertificate_graph (code s b f t g lo z:V) :
    totalityCertificateGraph.val.Evalb ![code,s,b,f,t,g,lo,z] ↔
      verifyValue code=translate (parameters 0 g lo z) (guardedTotalityCode s b f t)+1 := by
  simp [totalityCertificateGraph,guardedTotality_graph,parameters_graph,translate_graph,verify_graph,eq_comm,Matrix.comp_vecCons'']
attribute [local irreducible] totalityCertificateGraph
noncomputable def totalityInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s b f, !supportedValueEnvironmentGraph s b f t → ∀ g lo z p,
    !guardedTotalityGraph p s b f t → !coverageGraph 0 g lo z p →
    ∃ code, !totalityCertificateGraph code s b f t g lo z”
theorem totality_invariant (k:V) : totalityInvariant.Evalb ![k] ↔
    ∀t<k, ValueSupply (V:=V) t := by
  simp [totalityInvariant,ValueSupply,supportedValueEnvironment_graph,guardedTotality_graph,
    coverage_graph,totalityCertificate_graph,Matrix.comp_vecCons'']

#print axioms totalityCertificate_graph
#print axioms totality_invariant
end M6.PA.NumericPAeqSupportedValueTotality

