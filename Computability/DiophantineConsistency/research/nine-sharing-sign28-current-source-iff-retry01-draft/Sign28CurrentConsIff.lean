import DiophantineConsistency.Sign28CurrentSeedIff

/-! Uncompiled narrow-import cons-form seed equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28CurrentConsIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  SharingSeed28Sextic.seed SharingSeed31Sextic.seed CurrentWindowCarry2011.ports

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

theorem seed_cons_iff :
    (∃ w : Fin 28 → V, InternalZero (SharingSeed28Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)) ↔
    (∃ w : Fin 31 → V, InternalZero (SharingSeed31Sextic.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)) := by
  have h28 := exists_cons_iff (V := V) (fun v : Fin 29 → V => InternalZero (SharingSeed28Sextic.seed CurrentWindowCarry2011.ports) v)
  have h31 := exists_cons_iff (V := V) (fun v : Fin 32 → V => InternalZero (SharingSeed31Sextic.seed CurrentWindowCarry2011.ports) v)
  exact h28.trans ((Sign28CurrentSeedIff.exists_same_input (1 : V)).trans h31.symm)
end DiophantineConsistency.Sign28CurrentConsIff
#print axioms DiophantineConsistency.Sign28CurrentConsIff.exists_cons_iff
#print axioms DiophantineConsistency.Sign28CurrentConsIff.seed_cons_iff
