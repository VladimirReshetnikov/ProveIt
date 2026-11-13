import DiophantineConsistency.Sign28ReverseBridge

/-! SOURCE-ONLY candidate; its zero-bridge import is not yet checked. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem drop_lift (beta : V) (v : Fin 29 → V) :
    Sign28CoordinateRecover.drop (Sign28FirstCuts.lift beta v) = v := by
  funext j
  fin_cases j <;> simp [Sign28CoordinateRecover.drop, Sign28FirstCuts.lift]

theorem pointwise (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    InternalZero (SharingSeed28Sextic.seed p) v ↔
      InternalZero (SharingSeed31Sextic.seed p) (Sign28FirstCuts.lift beta v) := by
  constructor
  · exact Sign28ZeroBridge.forward p beta v hp0
  · intro hz
    have h := Sign28ZeroBridge.backward p beta (Sign28FirstCuts.lift beta v) hp0 hz
    simpa only [drop_lift] using h
end DiophantineConsistency.Sign28SeedIff
#print axioms DiophantineConsistency.Sign28SeedIff.drop_lift
#print axioms DiophantineConsistency.Sign28SeedIff.pointwise
