module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueUniquenessInput
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def uniquenessCode (s b f t:V):V :=
  imp language (inputDomain s b f) (comparisonCode b b f f t)
theorem guarded_value_uniqueness_certificate {s b f t:V} (h:ValueEnvironment s b f t) (native lo z:V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (uniquenessCode s b f t)):
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (uniquenessCode s b f t)+1 := by
  apply source_implication_compose _ (coherenceInput s b b f f) _ native lo z (inputDomain_valid h)
    (coherenceInput_valid ⟨h,h⟩) (comparisonCode_valid ⟨h,h⟩) hc
  · intro native lo z hc; exact diagonal_input_certificate h native lo z hc
  · intro native lo z hc; exact guarded_value_coherence_certificate ⟨h,h⟩ native lo z hc
attribute [local irreducible] NumericPAeqValueDomainGuard.guardGraph comparisonGraph
noncomputable def uniquenessGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out s b f t. ∃ k left right antecedent consequent,
    !lenDef k f ∧ !NumericPAeqValueDomainGuard.guardGraph left b s ∧
    !NumericPAeqValueDomainGuard.guardGraph right f k ∧ !qqAndDef antecedent left right ∧
    !comparisonGraph consequent b b f f t ∧ !(impGraph language) out antecedent consequent”
theorem uniqueness_graph (out s b f t:V):uniquenessGraph.val.Evalb ![out,s,b,f,t] ↔ out=uniquenessCode s b f t := by
  simp [uniquenessGraph,uniquenessCode,inputDomain,NumericPAeqValueDomainGuard.guard_graph,comparison_graph,Matrix.comp_vecCons'']
attribute [local irreducible] uniquenessGraph RelationalSource.Numeric.parametersGraph RelationalSource.Numeric.translateGraph verifyGraph
noncomputable def uniquenessCertificateGraph : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
  “code s b f t native lo z. ∃ p param out, !uniquenessGraph p s b f t ∧
    !RelationalSource.Numeric.parametersGraph param 0 native lo z ∧
    !RelationalSource.Numeric.translateGraph out param p ∧ !verifyGraph (out+1) code”
theorem uniquenessCertificate_graph (code s b f t native lo z:V):
    uniquenessCertificateGraph.val.Evalb ![code,s,b,f,t,native,lo,z] ↔
      verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z) (uniquenessCode s b f t)+1 := by
  simp [uniquenessCertificateGraph,uniqueness_graph,RelationalSource.Numeric.parameters_graph,
    RelationalSource.Numeric.translate_graph,verify_graph,eq_comm,Matrix.comp_vecCons'']
#print axioms guarded_value_uniqueness_certificate
#print axioms uniqueness_graph
#print axioms uniquenessCertificate_graph
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
