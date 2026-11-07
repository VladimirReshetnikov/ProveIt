import DiophantineConsistency.Sign31ReverseBridge

/-! UNCOMPILED symbolic pointwise zero equivalence under the f² lift. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem drop_lift (v : Fin 32 → V) :
    Sign31CoordinateRecover.drop (Sign31FirstCut.lift v) = v := by
  funext j
  fin_cases j <;> simp [Sign31CoordinateRecover.drop, Sign31FirstCut.lift]

theorem pointwise (p : Fin 4 → ℤ) (v : Fin 32 → V) :
    InternalZero (SharingSeed31Sextic.seed p) v ↔
      InternalZero (SharingSeed32Sextic.seed p) (Sign31FirstCut.lift v) := by
  constructor
  · exact Sign31ZeroBridge.forward p v
  · intro hz
    have h := Sign31ZeroBridge.backward p (Sign31FirstCut.lift v) hz
    simpa only [drop_lift] using h
end DiophantineConsistency.Sign31SeedIff
#print axioms DiophantineConsistency.Sign31SeedIff.drop_lift
#print axioms DiophantineConsistency.Sign31SeedIff.pointwise
