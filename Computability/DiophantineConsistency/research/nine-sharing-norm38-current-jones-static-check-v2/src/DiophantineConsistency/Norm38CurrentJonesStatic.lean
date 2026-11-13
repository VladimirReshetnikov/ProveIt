import DiophantineConsistency.Norm38CurrentFourCastInstantiation
import DiophantineConsistency.SharingSeed38CurrentJones

/-! Candidate composition: nine-coordinate Jones zero iff static constraints.
No Carrier65 or iPRA endpoint is asserted. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentJonesStatic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem current_nine_zero_iff_static :
    (∃ a : Fin 9 → V,
      (ExecutableJones.expression (SharingSeed38.seed CurrentWindowCarry2011.ports) 0).evalRing
        (fun i => ι (a i)) = 0) ↔
    ∃ w : Fin 38 → V,
      NormAssignment38.gatesHold ι (Norm38CurrentFourCastInstantiation.currentNaturalPorts (V := V)) w ∧
        NormAssignment38.fiveNorms ι (Norm38CurrentFourCastInstantiation.currentNaturalPorts (V := V)) w := by
  constructor
  · intro hnine
    obtain ⟨w, hw⟩ := (SharingSeed38CurrentJones.current_nine_iff (V := V)).mp hnine
    exact ⟨w, (Norm38CurrentFourCastInstantiation.current_seed_zero_iff_static w).mp
      ((internalZero_iff _ _).mpr hw)⟩
  · rintro ⟨w, hw⟩
    apply (SharingSeed38CurrentJones.current_nine_iff (V := V)).mpr
    exact ⟨w, (internalZero_iff _ _).mp
      ((Norm38CurrentFourCastInstantiation.current_seed_zero_iff_static w).mpr hw)⟩
end DiophantineConsistency.Norm38CurrentJonesStatic
#print axioms DiophantineConsistency.Norm38CurrentJonesStatic.current_nine_zero_iff_static
