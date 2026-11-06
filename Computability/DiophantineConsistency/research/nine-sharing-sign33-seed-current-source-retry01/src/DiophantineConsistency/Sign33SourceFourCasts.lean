import DiophantineConsistency.Sign33SeedSource
import DiophantineConsistency.Norm38FourVariablePorts

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33SourceFourCasts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_implies_source (b k l h : V) (v : Fin 34 → V)
    (h0 : ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = ι b)
    (h1 : ((CurrentWindowCarry2011.ports 1 : ℤ) : DiffRing V) = ι k)
    (h2 : ((CurrentWindowCarry2011.ports 2 : ℤ) : DiffRing V) = ι l)
    (h3 : ((CurrentWindowCarry2011.ports 3 : ℤ) : DiffRing V) = ι h)
    (hz : InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) v) :
    InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)
      (fun j => v (Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)) + 1) := by
  exact Sign33SeedSource.seed_implies_source CurrentWindowCarry2011.ports
    (Norm38FourVariablePorts.naturalPorts b k l h) v h0 h1 h2 h3 hz
end DiophantineConsistency.Sign33SourceFourCasts
#print axioms DiophantineConsistency.Sign33SourceFourCasts.seed_implies_source
