module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueDiagonalGuard
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] NumericPAeqValueDomainGuard.guardGraph NumericPAeqValueIsoGuard.guardGraph parametersGraph translateGraph verifyGraph coverageGraph
noncomputable def diagonalGuardGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out env count. ∃ d i, !NumericPAeqValueDomainGuard.guardGraph d env count ∧
    !NumericPAeqValueIsoGuard.guardGraph i env env count ∧ !(impGraph RelationalSource.language) out d i”
theorem diagonalGuard_graph (out env count:V):diagonalGuardGraph.val.Evalb ![out,env,count] ↔ out=diagonalGuardCode env count := by
  simp [diagonalGuardGraph,diagonalGuardCode,NumericPAeqValueDomainGuard.guard_graph,
    NumericPAeqValueIsoGuard.guard_graph,Matrix.comp_vecCons'']
attribute [local irreducible] diagonalGuardGraph
noncomputable def diagonalCertificateGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “code env count native lo z. ∃ p param out, !diagonalGuardGraph p env count ∧
    !parametersGraph param 0 native lo z ∧ !translateGraph out param p ∧ !verifyGraph (out+1) code”
theorem diagonalCertificate_graph (code env count native lo z:V):
    diagonalCertificateGraph.val.Evalb ![code,env,count,native,lo,z] ↔
      verifyValue code=translate (parameters 0 native lo z) (diagonalGuardCode env count)+1 := by
  simp [diagonalCertificateGraph,diagonalGuard_graph,parameters_graph,translate_graph,verify_graph,eq_comm,Matrix.comp_vecCons'']
attribute [local irreducible] diagonalCertificateGraph
noncomputable def diagonalInvariant : ArithmeticSemisentence 1 :=
  “count. ∀env, (∀i<count, ∃t, !nthDef t env i ∧ !((isSemiterm RelationalSource.language).sigma) 0 t) →
    ∀native lo z p, !diagonalGuardGraph p env count → !coverageGraph 0 native lo z p →
    ∃code, !diagonalCertificateGraph code env count native lo z”
theorem diagonal_invariant (count:V):diagonalInvariant.Evalb ![count] ↔ DiagonalSupply (V:=V) count := by
  simp [diagonalInvariant,DiagonalSupply,diagonalGuard_graph,coverage_graph,diagonalCertificate_graph,Matrix.comp_vecCons'']
#print axioms diagonalGuard_graph
#print axioms diagonalCertificate_graph
#print axioms diagonal_invariant
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
