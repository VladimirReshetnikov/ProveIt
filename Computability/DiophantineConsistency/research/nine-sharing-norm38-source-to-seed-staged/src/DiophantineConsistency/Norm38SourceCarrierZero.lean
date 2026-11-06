import FreshModel106

/-! Candidate conversion of source syntax zero to its Carrier65 ring value. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SourceCarrierZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_zero_carrier (p : Fin 4 → ℤ) (ports : Fin 4 → V) (u : Fin 14 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hs : InternalZero (ObjectCurrentEquation2011.expressionAt p) (fun j => u j+1)) :
    Carrier65.value (fun j => ι (ports j)) (fun j => ι (u j+1)) = 0 := by
  rw [internalZero_iff, FreshModel106.evalRing_expressionAt65] at hs
  simpa only [hp] using hs
end DiophantineConsistency.Norm38SourceCarrierZero
#print axioms DiophantineConsistency.Norm38SourceCarrierZero.source_zero_carrier
