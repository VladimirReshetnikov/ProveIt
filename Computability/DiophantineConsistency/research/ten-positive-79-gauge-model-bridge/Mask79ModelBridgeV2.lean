import Mask79ActualOutput
import DiophantineConsistency.ModelDifferenceRing
import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-! Carry the arbitrary-ring gauge to model zeros given an explicit lifted valuation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mask79ModelBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive79Mask Mask79ActualRows Mask79ActualOutput
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def integerPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun j => (p j : ℤ)

theorem zero_preserved_of_lift (p : Fin 4 → ℕ) (v w : Fin 10 → V) (t : DiffRing V)
    (hcast : let vv := fun j => ι (v j)
      let s := shared (integerPorts p) vv (rankTerm (integerPorts p) vv)
      move vv s t = fun j => ι (w j))
    (hz : InternalZero (output79 (integerPorts p)) v) :
    InternalZero (output79 (integerPorts p)) w := by
  apply (internalZero_iff _ _).mpr
  rw [← hcast, output_move]
  exact (internalZero_iff _ _).mp hz

#print axioms Mask79ModelBridge.zero_preserved_of_lift
end Mask79ModelBridge
