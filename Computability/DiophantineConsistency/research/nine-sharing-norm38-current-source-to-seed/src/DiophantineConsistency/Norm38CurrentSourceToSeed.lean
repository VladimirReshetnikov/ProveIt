import DiophantineConsistency.Norm38SourceCarrierZero
import DiophantineConsistency.Norm38FixedPortNorms
import DiophantineConsistency.Norm38ForwardFiveNorms
import DiophantineConsistency.Norm38ForwardGatesAssembly
import DiophantineConsistency.Norm38StaticToSeed

/-! Fixed-current-port source-zero-to-seed-zero composition. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38CurrentSourceToSeed
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_zero_implies_seed_zero (ports : Fin 4 → V) (u : Fin 14 → V)
    (hp : ∀ j, ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (ports j))
    (hs : InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)
      (fun j => u j+1)) :
    InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports)
      (Fin.cons (1 : V) (SharingForward38.witnessCoordinates ports u)) := by
  have hvalue := Norm38SourceCarrierZero.source_zero_carrier CurrentWindowCarry2011.ports ports u hp hs
  have hports : (fun j => ι (ports j)) = Norm38FixedPortNorms.ringPorts := by
    funext j
    exact (hp j).symm
  rw [hports] at hvalue
  have hx : ∀ j, (0 : DiffRing V) < ι (u j+1) := fun j =>
    ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
  have hnorm := Norm38FixedPortNorms.carrier_zero_unitNorms (fun j => ι (u j+1)) hx hvalue
  rw [← hports] at hnorm
  exact Norm38Forward.static_implies_seed_zero CurrentWindowCarry2011.ports ports _ hp
    (Norm38ForwardGates.forward_gatesHold ι ports u)
    (Norm38ForwardFiveNorms.forward_fiveNorms ports u hnorm)
end DiophantineConsistency.Norm38CurrentSourceToSeed
#print axioms DiophantineConsistency.Norm38CurrentSourceToSeed.source_zero_implies_seed_zero
