module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherenceSupply
public import PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherenceSuccessorStep
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqSupportedValueCoherence

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueTotality NumericPAeqValueCoherence
open NumericPAeqSupportedValueTotality PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem coherence_successor_step {u:V} (ihu:SupportedCoherenceSupply (V:=V) u):
    SupportedCoherenceSupply (V:=V) (qqFunc 1 1 (u∷0)) := by
  intro s b c f g h native lo z hc
  have hu : IsSemiterm Presentation.language s u := IsSemitermVec.singleton.mp (IsSemiterm.func.mp h.1.2.2.1).2
  have he := (show SupportedCoherenceEnvironment s b c f g u from by simpa using coherenceEnvironment_at h (show (0:V)<1 by simp))
  apply source_implication_compose (coherenceInput s b c f g) (comparisonCode b c f g u)
    (comparisonCode b c f g (qqFunc 1 1 (u∷0))) native lo z (coherenceInput_valid h)
    (comparisonCode_valid he) (comparisonCode_valid h) hc
  · intro native lo z hc; exact ihu s b c f g he native lo z hc
  · intro native lo z hc; exact successor_comparison_certificate he native lo z hc
#print axioms coherence_successor_step
end PA196.Arithmetic.Transport.NumericPAeqSupportedValueCoherence
