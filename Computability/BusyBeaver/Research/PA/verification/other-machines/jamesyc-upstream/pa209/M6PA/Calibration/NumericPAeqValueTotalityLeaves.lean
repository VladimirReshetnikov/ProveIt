module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueTotalitySyntax
public import M6PA.Calibration.RelationalPredicateTemplateVariableApplication
public import M6PA.Calibration.RelationalClosedCertificateSupply
@[expose] public section

/-! Exact leaf constructor joins. Variable branches still require the domain
antecedent; zero uses the already paid closed inhabited-zero theorem. -/
namespace M6.PA.NumericPAeqValueTotality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm ActualCheckerBlueprint
open ActualCertificateConstructors.Dominated
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem valueTotality_bvar {b f i k n : V} (hb:IsSemitermVec language k n b) (hi:i<k) :
    valueTotalityCode b f (qqBvar i)=RelationalPredicateTemplate.Variable.variableOutput (nth b i) := by
  simp only [valueTotalityCode,valueSyntax_bvar,parameters_result,parameters_bound,
    shiftTerms_nth hb hi,RelationalPredicateTemplate.Variable.variableOutput]

theorem valueTotality_fvar {b f i k n : V} (hf:IsSemitermVec language k n f) (hi:i<k) :
    valueTotalityCode b f (qqFvar i)=RelationalPredicateTemplate.Variable.variableOutput (nth f i) := by
  simp only [valueTotalityCode,valueSyntax_fvar,parameters_result,parameters_free,
    shiftTerms_nth hf hi,RelationalPredicateTemplate.Variable.variableOutput]

theorem valueTotality_zero (b f : V) :
    valueTotalityCode b f (qqFunc 0 0 0)=(⌜ForwardRelational.zeroInhabited⌝ : V) := by
  simp only [valueTotalityCode,valueSyntax_zero,parameters_result]
  have h := zeroValue_quote (V:=V) (.bvar 0 : RelationalSource.Ordinal.Term 1)
  have hz : (qqBvar (0:V))=(⌜(.bvar 0 : RelationalSource.Ordinal.Term 1)⌝ : V) := by simp
  rw [hz,h]
  rfl

theorem zero_requested_certificate (b f g lo z : V)
    (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z (valueTotalityCode b f (qqFunc 0 0 0))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z)
      (valueTotalityCode b f (qqFunc 0 0 0))+1 := by
  rw [valueTotality_zero] at hc ⊢
  exact RelationalClosedCertificate.zero_certificate g lo z hc

theorem bound_variable_from_guard {b f k i g lo z : V}
    (hb:IsSemitermVec language k 0 b) (hi:i<k)
    (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z (RelationalPredicateTemplate.Variable.variableTotalityCode (nth b i))) :
    ∃code,verifyValue code=wim
      (RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z) (NumericPAeqValueDomainGuard.guard b k))
      (RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z) (valueTotalityCode b f (qqBvar i)))+1 := by
  rw [valueTotality_bvar hb hi]
  exact RelationalPredicateTemplate.Variable.variable_from_guard_certificate b k i g lo z hi (fun j hj => hb.nth hj) hc

theorem free_variable_from_guard {b f k i g lo z : V}
    (hf:IsSemitermVec language k 0 f) (hi:i<k)
    (hc:RelationalSource.Numeric.FormulaCovered 0 g lo z (RelationalPredicateTemplate.Variable.variableTotalityCode (nth f i))) :
    ∃code,verifyValue code=wim
      (RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z) (NumericPAeqValueDomainGuard.guard f k))
      (RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 g lo z) (valueTotalityCode b f (qqFvar i)))+1 := by
  rw [valueTotality_fvar hf hi]
  exact RelationalPredicateTemplate.Variable.variable_from_guard_certificate f k i g lo z hi (fun j hj => hf.nth hj) hc

#print axioms valueTotality_bvar
#print axioms valueTotality_fvar
#print axioms valueTotality_zero
#print axioms zero_requested_certificate
#print axioms bound_variable_from_guard
#print axioms free_variable_from_guard
end M6.PA.NumericPAeqValueTotality

