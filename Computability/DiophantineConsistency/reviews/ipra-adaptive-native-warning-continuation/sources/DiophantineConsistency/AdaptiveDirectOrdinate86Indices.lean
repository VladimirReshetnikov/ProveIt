import DiophantineConsistency.AdaptiveDirectOrdinate86MainOrientation
import DiophantineConsistency.ArithmeticAdaptivePellIndices2011

/-! First and main Pell indices from the actual direct-ordinate zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Indices
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptivePellIndices2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Quotients AdaptiveDirectOrdinate86MainOrientation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem expressionAt_indices86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : Indices p v :=
  indices_of_quotients p v hv (expressionAt_quotients86 p v hb hv hz)
    (expressionAt_main_oriented86 p v hb hv hz)
end DiophantineConsistency.AdaptiveDirectOrdinate86Indices
