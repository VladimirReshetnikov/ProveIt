module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceSupply
public import PA196.Arithmetic.Transport.NumericPAeqValueCoherenceSuccessorStep
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
theorem coherence_successor_step {u:V} (ihu:CoherenceSupply (V:=V) u):
    CoherenceSupply (V:=V) (qqFunc 1 1 (u∷0)) := by
  intro s b c f g h native lo z hc
  have hu : IsSemiterm Presentation.language s u := IsSemitermVec.singleton.mp (IsSemiterm.func.mp h.1.2.2.1).2
  have he := coherenceEnvironment_child h hu (unary_child_rank u)
  apply source_implication_compose (coherenceInput s b c f g) (comparisonCode b c f g u)
    (comparisonCode b c f g (qqFunc 1 1 (u∷0))) native lo z (coherenceInput_valid h)
    (comparisonCode_valid he) (comparisonCode_valid h) hc
  · intro native lo z hc; exact ihu s b c f g he native lo z hc
  · intro native lo z hc; exact successor_comparison_certificate he native lo z hc
#print axioms coherence_successor_step
end PA196.Arithmetic.Transport.NumericPAeqValueCoherence
