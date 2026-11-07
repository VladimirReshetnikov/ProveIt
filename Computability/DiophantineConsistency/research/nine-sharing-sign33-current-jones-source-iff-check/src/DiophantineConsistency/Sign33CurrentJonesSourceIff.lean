import DiophantineConsistency.Sign33CurrentSeedIff
import DiophantineConsistency.SharingSeed33CurrentJones

/-! Current symbolic 33-seed Jones/source existential composition. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentJonesSourceIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem nine_exists_iff_source :
    (∃ a : Fin 9 → V,
      (ExecutableJones.expression (SharingSeed33.seed CurrentWindowCarry2011.ports) 0).evalRing
        (fun i => ι (a i)) = 0) ↔
    ∃ u : Fin 14 → V, InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  have hright :
      (∃ w : Fin 33 → V, (SharingSeed33.seed CurrentWindowCarry2011.ports).evalRing
        (fun j => ι ((Fin.cons (1 : V) w : Fin 34 → V) j)) = 0) ↔
      ∃ w : Fin 33 → V, InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) :=
    exists_congr fun w => (internalZero_iff (SharingSeed33.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)).symm
  exact (SharingSeed33CurrentJones.current_nine_iff (V := V)).trans
    (hright.trans (Sign33CurrentSeedIff.seed_exists_iff_source (V := V)))
end DiophantineConsistency.Sign33CurrentJonesSourceIff
#print axioms DiophantineConsistency.Sign33CurrentJonesSourceIff.nine_exists_iff_source
