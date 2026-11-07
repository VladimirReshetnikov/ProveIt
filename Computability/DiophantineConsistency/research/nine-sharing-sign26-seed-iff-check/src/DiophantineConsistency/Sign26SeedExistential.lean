import DiophantineConsistency.Sign26ReverseBridgeRetry

/-! SOURCE-ONLY: same-input seed equivalence under explicit port hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (beta K x : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K) (hbeta : 1 ≤ beta) :
    (∃ v : Fin 27 → V, v 0 = x ∧ InternalZero (SharingSeed26Sextic.seed p) v) ↔
      ∃ v : Fin 28 → V, v 0 = x ∧ InternalZero (SharingSeed27Sextic.seed p) v := by
  constructor
  · rintro ⟨v, hv, hz⟩
    obtain ⟨gap, _, hzero⟩ := Sign26ZeroBridge.forward p beta K v hp0 hp1 hbeta hz
    refine ⟨Sign26CongruenceCuts.lift gap v, ?_, hzero⟩
    simpa [Sign26CongruenceCuts.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign26ZeroBridge.drop v, ?_, Sign26ZeroBridge.backward p v hz⟩
    simpa [Sign26ZeroBridge.drop] using hv
end DiophantineConsistency.Sign26SeedIff
#print axioms DiophantineConsistency.Sign26SeedIff.exists_same_input
