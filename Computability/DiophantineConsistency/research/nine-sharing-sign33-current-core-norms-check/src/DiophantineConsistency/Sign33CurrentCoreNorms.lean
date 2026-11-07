import DiophantineConsistency.Norm38FixedPortNorms
import FreshModel106

/-! Five current source core norms with positively shifted model inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentCoreNorms
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_core_norms (u : Fin 14 → V)
    (hs : InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)
      (fun j => u j+1)) :
    let d := Carrier65.core (Norm38FixedPortNorms.ringPorts (V := V)) (fun j => ι (u j+1))
    d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1 := by
  rw [internalZero_iff, FreshModel106.evalRing_expressionAt65] at hs
  have hx : ∀ j, (0 : DiffRing V) < ι (u j+1) := fun j =>
    ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
  exact Norm38FixedPortNorms.carrier_zero_unitNorms (fun j => ι (u j+1)) hx hs
end DiophantineConsistency.Sign33CurrentCoreNorms
#print axioms DiophantineConsistency.Sign33CurrentCoreNorms.source_core_norms
