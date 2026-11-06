import DiophantineConsistency.Sign33ResidualIff
import DiophantineConsistency.Sign33AllCutsSource

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33SeedSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_implies_source (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι (ports 1))
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι (ports 2))
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι (ports 3))
    (hz : InternalZero (SharingSeed33.seed p) v) :
    InternalZero (ObjectCurrentEquation2011.expressionAt p)
      (fun j => v (Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)) + 1) := by
  have hc := (Sign33ResidualIff.seed_zero_iff_all_cuts p ports v hp0 hp1 hp2 hp3).mp hz
  exact Sign33AllCutsSource.allcuts_imply_source_zero p ports v hp0 hp1 hp2 hp3 hc
end DiophantineConsistency.Sign33SeedSource
#print axioms DiophantineConsistency.Sign33SeedSource.seed_implies_source
