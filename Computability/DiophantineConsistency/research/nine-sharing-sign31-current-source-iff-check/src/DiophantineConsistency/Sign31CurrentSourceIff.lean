import DiophantineConsistency.Sign31SeedExistential
import DiophantineConsistency.Sign32CurrentSourceIff

/-! UNCOMPILED composition of sign31/32 seed iff with the current source. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31CurrentSourceIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_exists_iff_source :
    (∃ w : Fin 31 → V, InternalZero (SharingSeed31Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)) ↔
      ∃ u : Fin 14 → V, ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  have h31 := Sign32CurrentSourceIff.exists_cons_iff (V := V) (fun v : Fin 32 → V => InternalZero (SharingSeed31Sextic.seed CurrentWindowCarry2011.ports) v)
  have h32 := Sign32CurrentSourceIff.exists_cons_iff (V := V) (fun v : Fin 33 → V => InternalZero (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports) v)
  exact h31.trans ((Sign31SeedIff.exists_same_input CurrentWindowCarry2011.ports (1 : V)).trans (h32.symm.trans Sign32CurrentSourceIff.seed_exists_iff_source))
end DiophantineConsistency.Sign31CurrentSourceIff
#print axioms DiophantineConsistency.Sign31CurrentSourceIff.seed_exists_iff_source
