module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceShape
public import M6PA.Calibration.NumericPAeqFormulaRecursion
public import PA196.Arithmetic.Transport.NumericPAeqFormulaEqualityTransportCode
public import M6PA.Calibration.NumericPAeqTermSupportedBoundInstance
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic


/-! Exact positive equality-atom shape at zero-arity target environments.
Only genuine free-variable support is required, never source-code bounds. -/
namespace PA196.Arithmetic.Transport.NumericPAeqFormulaEqualityValueShape
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqTerm NumericPAeqValueCoherence NumericPAeqFormulaEqualityTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem equality_value_instance {s b f t i : V}
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (ht:IsSemiterm Presentation.language s t) (hs:FreeSupported (len f) t) (hi:i<2) :
    valueSyntax (NumericPAeqFormula.equalityTermParameters (NumericPAeqFormula.parameters b f) i) t =
      substs1 language (qqBvar i) (valuePredicate b f t) := by
  rw [valuePredicate,valueSyntax_supported_bound_instance hb hf ht hs
    (show IsSemiterm language 2 (qqBvar i) from IsSemiterm.bvar.mpr hi)]
  simp [NumericPAeqFormula.equalityTermParameters,NumericPAeqFormula.parameters,
    shiftTerms_zero_arity hb,shiftTerms_zero_arity hf]

theorem equality_atom_value_shape {s b f t u : V}
    (hb:IsSemitermVec language s 0 b) (hf:IsSemitermVec language (len f) 0 f)
    (ht:IsSemiterm Presentation.language s t) (hu:IsSemiterm Presentation.language s u)
    (hs:FreeSupported (len f) t) (hsu:FreeSupported (len f) u) :
    NumericPAeqFormula.formulaSyntax (NumericPAeqFormula.parameters b f) (qqRel 2 0 (t∷(u∷0))) =
      equalityAtomCode (valuePredicate b f t) (valuePredicate b f u) := by
  rw [NumericPAeqFormula.formulaSyntax_rel _ _ _ _ (by simp)
    (IsUTermVec.two_iff.mpr ⟨t,u,ht.isUTerm,hu.isUTerm,rfl⟩)]
  simp only [NumericPAeqFormula.atomCode,nth_adjoin_zero]
  rw [show nth (t∷(u∷0)) 1=u by simp]
  rw [equality_value_instance hb hf ht hs (by simp),equality_value_instance hb hf hu hsu (by simp)]
  rfl
#print axioms equality_value_instance
#print axioms equality_atom_value_shape
end PA196.Arithmetic.Transport.NumericPAeqFormulaEqualityValueShape

