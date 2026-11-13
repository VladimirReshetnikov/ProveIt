import DiophantineConsistency.Norm38SeedSource
import DiophantineConsistency.Norm38FourVariablePorts

/-! Parametric four-cast application; no concrete coefficients. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38FourCastSeedSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_implies_source (p : Fin 4 → ℤ) (b k l h : V) (w : Fin 38 → V)
    (h0 : ((p 0 : ℤ) : DiffRing V) = ι b)
    (h1 : ((p 1 : ℤ) : DiffRing V) = ι k)
    (h2 : ((p 2 : ℤ) : DiffRing V) = ι l)
    (h3 : ((p 3 : ℤ) : DiffRing V) = ι h)
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    InternalZero (ObjectCurrentEquation2011.expressionAt p)
      (fun j => w (Fin.castLE (by decide : 14 ≤ 38) j) + 1) := by
  exact Norm38SeedSource.seed_zero_implies_source_zero p
    (Norm38FourVariablePorts.naturalPorts b k l h) w
    (Norm38FourVariablePorts.casts_of_four p b k l h h0 h1 h2 h3) hz

end DiophantineConsistency.Norm38FourCastSeedSource
#print axioms DiophantineConsistency.Norm38FourCastSeedSource.seed_implies_source
