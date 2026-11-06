import DiophantineConsistency.Norm38CurrentSeedSource
import DiophantineConsistency.SharingSeed38CurrentJones

/-! Source-only proposal for the nine-zero to source-zero implication. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentNineSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem current_nine_implies_source
    (hnine : ∃ a : Fin 9 → V,
      (ExecutableJones.expression (SharingSeed38.seed CurrentWindowCarry2011.ports) 0).evalRing
        (fun i => ι (a i)) = 0) :
    ∃ v : Fin 14 → V,
      InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports) v := by
  obtain ⟨w, hw⟩ := (SharingSeed38CurrentJones.current_nine_iff (V := V)).mp hnine
  exact ⟨(fun j => w (Fin.castLE (by decide : 14 ≤ 38) j) + 1),
    Norm38CurrentSeedSource.current_seed_implies_source w ((internalZero_iff _ _).mpr hw)⟩

end DiophantineConsistency.Norm38CurrentNineSource
#print axioms DiophantineConsistency.Norm38CurrentNineSource.current_nine_implies_source
