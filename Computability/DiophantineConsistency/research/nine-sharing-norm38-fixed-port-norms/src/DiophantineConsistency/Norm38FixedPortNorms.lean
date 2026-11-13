import FreshCarrierSpheres

/-! Norm extraction at the concrete current ports, with abstract positive ring inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38FixedPortNorms
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev ringPorts : Fin 4 → DiffRing V := fun j => ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V)

theorem carrier_zero_unitNorms (x : Fin 14 → DiffRing V)
    (hx : ∀ j, (0 : DiffRing V) < x j)
    (hz65 : Carrier65.value ringPorts x = 0) :
    let d := Carrier65.core ringPorts x
    d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1 := by
  have hb : (0 : DiffRing V) < ringPorts 0 := FreshModel106.beta_pos
  exact (value65_zero_iff_norms modelFacts ringPorts x hb hx).mp hz65
end DiophantineConsistency.Norm38FixedPortNorms
#print axioms DiophantineConsistency.Norm38FixedPortNorms.carrier_zero_unitNorms
