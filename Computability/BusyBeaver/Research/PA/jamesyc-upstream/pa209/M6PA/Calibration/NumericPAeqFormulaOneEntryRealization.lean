module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaOneEntryInput
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueVectorRealization
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def oneEntryCode (r b f p u x:V):V :=
  imp language (oneEntryInput r b f u x) (formulaComparison b f (x∷0) (u∷0) p)
theorem oneEntry_environment {r b f p u x:V} (hb:IsSemitermVec language r 0 b)
    (hf:IsSemitermVec language (len f) 0 f) (hp:IsSemiformula Presentation.language 1 p)
    (hu:IsSemiterm Presentation.language r u) (hps:NumericPAeqFormula.FreeSupported (len f) p)
    (hus:FreeSupported (len f) u) (hx:IsSemiterm language 0 x):
    FormulaEnvironment 1 r b f (x∷0) (u∷0) p := by
  refine ⟨hb,hf,IsSemitermVec.singleton.mpr hx,hp,IsSemitermVec.singleton.mpr hu,hps,?_⟩
  intro i hi
  have he : i=0 := by simpa using hi
  subst i; simpa using hus
theorem one_entry_formula_certificate {r b f p u x:V} (hb:IsSemitermVec language r 0 b)
    (hf:IsSemitermVec language (len f) 0 f) (hp:IsSemiformula Presentation.language 1 p)
    (hu:IsSemiterm Presentation.language r u) (hps:NumericPAeqFormula.FreeSupported (len f) p)
    (hus:FreeSupported (len f) u) (hx:IsSemiterm language 0 x)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (oneEntryCode r b f p u x)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (oneEntryCode r b f p u x)+1 := by
  have he := oneEntry_environment hb hf hp hu hps hus hx
  apply source_implication_compose _ (vectorInput 1 r b f (x∷0) (u∷0)) _ native lo z
    (oneEntryInput_valid hb hf hu hus hx) (input_valid he) (formulaComparison_valid he) hc
  · exact oneEntryInput_certificate hb hf hu hus hx
  · exact open_source_formula_realization_certificate he
#print axioms oneEntry_environment
#print axioms one_entry_formula_certificate
end M6.PA.NumericPAeqFormulaRealization

