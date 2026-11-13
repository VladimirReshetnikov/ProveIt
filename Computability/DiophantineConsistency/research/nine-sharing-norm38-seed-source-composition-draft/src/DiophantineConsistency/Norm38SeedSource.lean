import DiophantineConsistency.Norm38SeedStaticIff
import DiophantineConsistency.Norm38StaticSource

/-! Source-only draft: seed zero implies source zero at the same witness. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38SeedSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_implies_source_zero
    (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    InternalZero (ObjectCurrentEquation2011.expressionAt p)
      (fun j => w (Fin.castLE (by decide : 14 ≤ 38) j) + 1) := by
  obtain ⟨hg, hn⟩ := (Norm38SeedStaticIff.seed_zero_iff_static p ports w hp).mp hz
  exact Norm38Reference.static_implies_source_zero p ports w hp hg hn

end DiophantineConsistency.Norm38SeedSource
#print axioms DiophantineConsistency.Norm38SeedSource.seed_zero_implies_source_zero
