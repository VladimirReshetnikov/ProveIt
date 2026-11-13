import DiophantineConsistency.Sign33CurrentSourceSeedCastFree
import DiophantineConsistency.Sign33CurrentSeedSourceRetry

/-! Source-only candidate for the current source/33-seed existential equivalence. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentSeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_exists_iff_source :
    (∃ w : Fin 33 → V, InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)) ↔
    ∃ u : Fin 14 → V, ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  constructor
  · rintro ⟨w,hw⟩
    let v : Fin 34 → V := Fin.cons (1 : V) w
    let u : Fin 14 → V := fun j => v (Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j))
    refine ⟨u, ?_⟩
    apply (ObjectCurrentEquation2011.internalZero_positiveShift ObjectCurrentEquation2011.expression u).mpr
    exact Sign33CurrentSeedSourceRetry.current_seed_implies_source v hw
  · rintro ⟨u,hu⟩
    exact Sign33CurrentSourceSeedCastFree.current_source_implies_seed u hu
end DiophantineConsistency.Sign33CurrentSeedIff
#print axioms DiophantineConsistency.Sign33CurrentSeedIff.seed_exists_iff_source
