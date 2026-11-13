module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSingletonRealization
@[expose] public section
namespace M6.PA.NumericPAeqFormulaRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm
open RelationalSource.Numeric ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def zeroInstanceCode (f p x:V):V :=
  imp language (qqAnd (NumericPAeqValueDomainGuard.guard f (len f)) (qqAnd (domainCode x) (zeroCode x)))
    (formulaComparison 0 f (x∷0) ((qqFunc 0 0 0)∷0) p)
theorem zeroInstance_eq (f p x:V):zeroInstanceCode f p x=singletonCode f p (qqFunc 0 0 0) x := by
  simp only [zeroInstanceCode,singletonCode,singletonInput,valueSyntax_zero,parameters_result,zeroValue]
theorem zero_instance_formula_certificate {f p x:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:NumericPAeqFormula.FreeSupported (len f) p)
    (hx:IsSemiterm language 0 x) (native lo z:V)
    (hc:FormulaCovered 0 native lo z (zeroInstanceCode f p x)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (zeroInstanceCode f p x)+1 := by
  have hz : FreeSupported (len f) (qqFunc 0 0 0) :=
    (freeSupported_func (show Presentation.language.IsFunc (0:V) 0 by simp)
      (show IsUTermVec Presentation.language (0:V) 0 by simp)).mpr (by simp)
  rw [zeroInstance_eq] at hc ⊢
  exact singleton_source_formula_certificate ⟨hf,hp,by simp,hs,hz,hx⟩ native lo z hc
#print axioms zeroInstance_eq
#print axioms zero_instance_formula_certificate
end M6.PA.NumericPAeqFormulaRealization

