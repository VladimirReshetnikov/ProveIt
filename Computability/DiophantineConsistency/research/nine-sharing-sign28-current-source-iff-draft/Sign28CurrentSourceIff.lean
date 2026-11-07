import DiophantineConsistency.Sign28CurrentSeedIff
import DiophantineConsistency.Sign31CurrentSourceIff

/-! SOURCE-ONLY proposed composition with current source. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28CurrentSourceIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_exists_iff_source :
    (∃ w : Fin 28 → V, InternalZero (SharingSeed28Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)) ↔
      ∃ u : Fin 14 → V, ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  have h28 := Sign32CurrentSourceIff.exists_cons_iff (V := V) (fun v : Fin 29 → V => InternalZero (SharingSeed28Sextic.seed CurrentWindowCarry2011.ports) v)
  have h31 := Sign32CurrentSourceIff.exists_cons_iff (V := V) (fun v : Fin 32 → V => InternalZero (SharingSeed31Sextic.seed CurrentWindowCarry2011.ports) v)
  exact h28.trans ((Sign28CurrentSeedIff.exists_same_input (1 : V)).trans (h31.symm.trans Sign31CurrentSourceIff.seed_exists_iff_source))
end DiophantineConsistency.Sign28CurrentSourceIff
#print axioms DiophantineConsistency.Sign28CurrentSourceIff.seed_exists_iff_source
