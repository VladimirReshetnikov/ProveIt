module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaAtomParameters
public import M6PA.Calibration.NumericPAeqTermFunction
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def atomCode (param _k _r ts : V) : V :=
  equalityCode
    (NumericPAeqTerm.valueSyntax (equalityTermParameters param 1) (nth ts 0))
    (NumericPAeqTerm.valueSyntax (equalityTermParameters param 0) (nth ts 1))

noncomputable def atomGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “out param k r ts. ∃ leftParam rightParam leftTerm rightTerm leftValue rightValue,
    !equalityTermParametersGraph leftParam param 1 ∧
    !equalityTermParametersGraph rightParam param 0 ∧
    !nthDef leftTerm ts 0 ∧ !nthDef rightTerm ts 1 ∧
    !NumericPAeqTerm.valueSyntaxGraph leftValue leftParam leftTerm ∧
    !NumericPAeqTerm.valueSyntaxGraph rightValue rightParam rightTerm ∧
    !equalityGraph out leftValue rightValue”

theorem atom_graph (out param k r ts : V) :
    atomGraph.val.Evalb ![out,param,k,r,ts] ↔ out=atomCode param k r ts := by
  simp [atomGraph,atomCode,equalityTermParameters_graph,NumericPAeqTerm.valueSyntax_graph,
    equality_graph,Matrix.comp_vecCons'']
instance atom_defined : 𝚺ᴬ₁-Function₄ (atomCode : V → V → V → V → V) via atomGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3,v 4]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! atom_graph (v 0) (v 1) (v 2) (v 3) (v 4)
theorem atom_total_unique (param k r ts : V) :
    ∃! out,atomGraph.val.Evalb ![out,param,k,r,ts] :=
  ⟨atomCode param k r ts,(atom_graph _ _ _ _ _).mpr rfl,
    fun _ h => (atom_graph _ _ _ _ _).mp h⟩
#print axioms atom_defined
#print axioms atom_total_unique
end M6.PA.NumericPAeqFormula

