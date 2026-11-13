module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceVariables
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceZero
public import PA196.Arithmetic.Transport.NumericPAeqValueGuardedSteps
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
def CoherenceSupply (t:V):Prop := ∀s b c f g:V, CoherenceEnvironment s b c f g t → ∀native lo z:V,
  RelationalSource.Numeric.FormulaCovered 0 native lo z (coherenceCode s b c f g t) →
  ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
    (coherenceCode s b c f g t)+1

theorem coherenceEnvironment_child {s b c f g t u:V} (h:CoherenceEnvironment s b c f g t)
    (hu:IsSemiterm Presentation.language s u) (hr:u<t):CoherenceEnvironment s b c f g u :=
  ⟨valueEnvironment_child h.1 hu hr,valueEnvironment_child h.2 hu hr⟩

theorem coherence_bvar_supply (i:V):CoherenceSupply (V:=V) (qqBvar i) := by
  intro s b c f g h native lo z hc
  exact coherence_bvar_certificate h native lo z hc
theorem coherence_fvar_supply (i:V):CoherenceSupply (V:=V) (qqFvar i) := by
  intro s b c f g h native lo z hc
  exact coherence_fvar_certificate h native lo z hc
theorem coherence_zero_supply : CoherenceSupply (V:=V) (qqFunc 0 0 0) := by
  intro s b c f g h native lo z hc
  exact coherence_zero_certificate h native lo z hc
#print axioms coherenceEnvironment_child
#print axioms coherence_bvar_supply
#print axioms coherence_fvar_supply
#print axioms coherence_zero_supply
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
