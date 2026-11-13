import DiophantineConsistency.CompactLowPopulation
import DiophantineConsistency.CompactSupportCard
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowExact
open CompactListMask CompactConcreteMask
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact population of the symbolic finite-list mask in every IΣ₁ model.
Identification with the retained MC payload and graph port is separate. -/
theorem model_population :
    population ((Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) : ℕ):V)=589083 :=
  CompactLowPopulation.model_population CompactSupportCard.support_card
end CompactLowExact
#print axioms CompactLowExact.model_population
