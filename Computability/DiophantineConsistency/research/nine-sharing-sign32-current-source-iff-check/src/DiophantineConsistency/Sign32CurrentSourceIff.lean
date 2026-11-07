import DiophantineConsistency.Sign32CurrentSeedIff
import DiophantineConsistency.Sign33CurrentSeedIff

/-! UNCOMPILED: compose current 32/33 seed equivalence with the current source. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32CurrentSourceIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_cons_iff {n : ℕ} (P : (Fin (n + 1) → V) → Prop) :
    (∃ w : Fin n → V, P (Fin.cons (1 : V) w)) ↔
      ∃ v : Fin (n + 1) → V, v 0 = 1 ∧ P v := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨Fin.cons 1 w, rfl, hw⟩
  · rintro ⟨v, hv, h⟩
    refine ⟨Fin.tail v, ?_⟩
    have hcons : Fin.cons (1 : V) (Fin.tail v) = v := by
      simpa only [hv] using (Fin.cons_self_tail v)
    simpa only [hcons] using h

theorem seed_exists_iff_source :
    (∃ w : Fin 32 → V, InternalZero (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)) ↔
      ∃ u : Fin 14 → V, ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u := by
  have h32 := exists_cons_iff (V := V) (fun v : Fin 33 → V => InternalZero (SharingSeed32Sextic.seed CurrentWindowCarry2011.ports) v)
  have h33 := exists_cons_iff (V := V) (fun v : Fin 34 → V => InternalZero (SharingSeed33.seed CurrentWindowCarry2011.ports) v)
  exact h32.trans ((Sign32CurrentSeedIff.exists_same_input (1 : V)).trans (h33.symm.trans Sign33CurrentSeedIff.seed_exists_iff_source))
end DiophantineConsistency.Sign32CurrentSourceIff
#print axioms DiophantineConsistency.Sign32CurrentSourceIff.exists_cons_iff
#print axioms DiophantineConsistency.Sign32CurrentSourceIff.seed_exists_iff_source
