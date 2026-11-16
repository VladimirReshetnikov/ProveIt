module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqGuardedUniversalCertificate
@[expose] public section
namespace M6.PA.NumericPAeqGuardedAlls
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqValueTotality NumericPAeqFormula ActualCheckerBlueprint
open RelationalSource.Numeric (FormulaCovered coverageGraph coverage_graph translate translateGraph translate_graph)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def matrixCode (s b f p:V):V :=
  imp language (inputDomain s b f) (formulaSyntax (NumericPAeqFormula.parameters b f) p)
def MatrixSupply (s p:V):Prop := ∀b f:V,
  IsSemitermVec language s 0 b→IsSemitermVec language (len f) 0 f→∀native lo z:V,
  FormulaCovered 0 native lo z (matrixCode s b f p)→
  ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (matrixCode s b f p)+1
attribute [local irreducible] NumericPAeqValueDomainGuard.guardGraph parametersGraph formulaSyntaxGraph
noncomputable def matrixGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out s b f p. ∃ l left right ant param con, !lenDef l f ∧
    !NumericPAeqValueDomainGuard.guardGraph left b s ∧ !NumericPAeqValueDomainGuard.guardGraph right f l ∧
    !qqAndDef ant left right ∧ !parametersGraph param b f ∧ !formulaSyntaxGraph con param p ∧
    !(impGraph language) out ant con”
theorem matrix_graph (out s b f p:V):matrixGraph.val.Evalb ![out,s,b,f,p] ↔out=matrixCode s b f p := by
  simp [matrixGraph,matrixCode,inputDomain,NumericPAeqValueDomainGuard.guard_graph,parameters_graph,
    formulaSyntax_graph,Matrix.comp_vecCons'']
attribute [local irreducible] matrixGraph RelationalSource.Numeric.coverageGraph RelationalSource.Numeric.parametersGraph translateGraph verifyGraph
noncomputable def matrixCertificateGraph : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
  “code s b f p native lo z. ∃ q param out, !matrixGraph q s b f p ∧
    !RelationalSource.Numeric.parametersGraph param 0 native lo z ∧ !translateGraph out param q ∧ !verifyGraph (out+1) code”
theorem matrixCertificate_graph (code s b f p native lo z:V):
    matrixCertificateGraph.val.Evalb ![code,s,b,f,p,native,lo,z] ↔
    verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (matrixCode s b f p)+1 := by
  simp [matrixCertificateGraph,matrix_graph,RelationalSource.Numeric.parameters_graph,translate_graph,
    verify_graph,eq_comm,Matrix.comp_vecCons'']
attribute [local irreducible] matrixCertificateGraph
noncomputable def matrixSupplyFormula : ArithmeticSemisentence 2 :=
  “s p. ∀ b f l, !lenDef l f → !((isSemitermVec language).sigma) s 0 b →
    !((isSemitermVec language).sigma) l 0 f → ∀ native lo z q,
    !matrixGraph q s b f p → !RelationalSource.Numeric.coverageGraph 0 native lo z q → ∃code,!matrixCertificateGraph code s b f p native lo z”
theorem matrixSupply_formula (s p:V):matrixSupplyFormula.Evalb ![s,p] ↔MatrixSupply s p := by
  simp [matrixSupplyFormula,MatrixSupply,matrix_graph,matrixCertificate_graph,RelationalSource.Numeric.coverage_graph,Matrix.comp_vecCons'']
#print axioms matrix_graph
#print axioms matrixCertificate_graph
#print axioms matrixSupply_formula
end M6.PA.NumericPAeqGuardedAlls

