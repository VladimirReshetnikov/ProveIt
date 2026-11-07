import DiophantineConsistency.Sign33CurrentSourceSeed
import DiophantineConsistency.Norm38FourVariablePorts

/-! Source-only candidate, generic four-port cast wrapper. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33SourceSeedFourCasts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_implies_seed (b k l h : V) (u : Fin 14 → V)
    (h0 : ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V) = ι b)
    (h1 : ((CurrentWindowCarry2011.ports 1 : ℤ) : DiffRing V) = ι k)
    (h2 : ((CurrentWindowCarry2011.ports 2 : ℤ) : DiffRing V) = ι l)
    (h3 : ((CurrentWindowCarry2011.ports 3 : ℤ) : DiffRing V) = ι h)
    (hz : ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u) :
    ∃ w : Fin 33 → V, InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) := by
  exact Sign33CurrentSourceSeed.source_implies_seed
    (Norm38FourVariablePorts.naturalPorts b k l h) u
    (Norm38FourVariablePorts.casts_of_four CurrentWindowCarry2011.ports b k l h h0 h1 h2 h3) hz
end DiophantineConsistency.Sign33SourceSeedFourCasts
#print axioms DiophantineConsistency.Sign33SourceSeedFourCasts.source_implies_seed
