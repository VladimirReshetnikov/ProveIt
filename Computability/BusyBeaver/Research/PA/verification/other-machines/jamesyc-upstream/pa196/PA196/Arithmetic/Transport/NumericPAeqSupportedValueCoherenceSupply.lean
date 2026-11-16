module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherenceVariables
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherenceZero
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqSupportedValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence PA196.Arithmetic.Checker
open NumericPAeqSupportedValueTotality
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
def SupportedCoherenceSupply (t:V):Prop := ∀s b c f g:V,SupportedCoherenceEnvironment s b c f g t→∀native lo z:V,
  RelationalSource.Numeric.FormulaCovered 0 native lo z (coherenceCode s b c f g t)→
  ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
    (coherenceCode s b c f g t)+1

theorem coherenceEnvironment_child {s b c f g t u:V} (h:SupportedCoherenceEnvironment s b c f g t)
    (hu:IsSemiterm Presentation.language s u) (hf:FreeSupported (len f) u) (hg:FreeSupported (len g) u):
    SupportedCoherenceEnvironment s b c f g u :=
  ⟨supportedValueEnvironment_child h.1 hu hf,supportedValueEnvironment_child h.2 hu hg⟩
theorem coherenceEnvironment_at {s b c f g k fn ts i:V}
    (h:SupportedCoherenceEnvironment s b c f g (qqFunc k fn ts)) (hi:i<k):
    SupportedCoherenceEnvironment s b c f g (nth ts i) := by
  have hv := IsSemiterm.func.mp h.1.2.2.1
  exact coherenceEnvironment_child h (hv.2.nth hi)
    ((freeSupported_func hv.1 hv.2.isUTerm).mp h.1.2.2.2 i hi)
    ((freeSupported_func hv.1 hv.2.isUTerm).mp h.2.2.2.2 i hi)

theorem coherence_bvar_supply (i:V):SupportedCoherenceSupply (V:=V) (qqBvar i) := by
  intro s b c f g h native lo z hc; exact coherence_bvar_certificate h native lo z hc
theorem coherence_fvar_supply (i:V):SupportedCoherenceSupply (V:=V) (qqFvar i) := by
  intro s b c f g h native lo z hc; exact coherence_fvar_certificate h native lo z hc
theorem coherence_zero_supply : SupportedCoherenceSupply (V:=V) (qqFunc 0 0 0) := by
  intro s b c f g h native lo z hc; exact coherence_zero_certificate h native lo z hc
#print axioms coherenceEnvironment_child
#print axioms coherenceEnvironment_at
#print axioms coherence_bvar_supply
end PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherence
