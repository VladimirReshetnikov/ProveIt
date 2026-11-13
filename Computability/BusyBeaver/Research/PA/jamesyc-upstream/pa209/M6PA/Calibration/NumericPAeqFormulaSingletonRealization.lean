module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSingletonInput
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
def SingletonEnvironment (f p u x:V):Prop :=
  IsSemitermVec language (len f) 0 f ∧ IsSemiformula Presentation.language 1 p ∧
  IsSemiterm Presentation.language 0 u ∧ NumericPAeqFormula.FreeSupported (len f) p ∧
  FreeSupported (len f) u ∧ IsSemiterm language 0 x
noncomputable def singletonCode (f p u x:V):V :=
  imp language (singletonInput f u x) (formulaComparison 0 f (x∷0) (u∷0) p)
theorem singleton_environment {f p u x:V} (h:SingletonEnvironment f p u x):
    FormulaEnvironment 1 0 0 f (x∷0) (u∷0) p := by
  refine ⟨by simp,h.1,IsSemitermVec.singleton.mpr h.2.2.2.2.2,h.2.1,
    IsSemitermVec.singleton.mpr h.2.2.1,h.2.2.2.1,?_⟩
  intro i hi
  have he : i=0 := by simpa using hi
  subst i
  simpa using h.2.2.2.2.1
theorem singletonCode_valid {f p u x:V} (h:SingletonEnvironment f p u x):IsFormula language (singletonCode f p u x) :=
  IsSemiformula.imp.mpr ⟨singletonInput_valid h.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2,
    formulaComparison_valid (singleton_environment h)⟩
theorem singleton_source_formula_certificate {f p u x:V} (h:SingletonEnvironment f p u x)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (singletonCode f p u x)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (singletonCode f p u x)+1 := by
  have he := singleton_environment h
  apply source_implication_compose _ (vectorInput 1 0 0 f (x∷0) (u∷0)) _ native lo z
    (singletonInput_valid h.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2) (input_valid he) (formulaComparison_valid he) hc
  · exact singletonInput_certificate h.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  · exact open_source_formula_realization_certificate he
#print axioms singleton_environment
#print axioms singletonCode_valid
#print axioms singleton_source_formula_certificate
end M6.PA.NumericPAeqFormulaRealization

