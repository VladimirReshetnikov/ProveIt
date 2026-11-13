import DiophantineConsistency.Norm38CurrentSourceFourCasts
import DiophantineConsistency.Norm38CurrentSeedSource
import DiophantineConsistency.SharingSeed38CurrentJones

/-! Source-only proposal for the current-port existential equivalences. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentCastFreeIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_exists_iff_shifted_source :
    (∃ w : Fin 38 → V,
      InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w)) ↔
    ∃ u : Fin 14 → V,
      InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)
        (fun j => u j + 1) := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨(fun j => w (Fin.castLE (by decide : 14 ≤ 38) j)),
      Norm38CurrentSeedSource.current_seed_implies_source w hw⟩
  · rintro ⟨u, hu⟩
    exact ⟨SharingForward38.witnessCoordinates
        (Norm38CurrentFourCastInstantiation.currentNaturalPorts (V := V)) u,
      Norm38CurrentSourceFourCasts.source_zero_implies_seed_zero u hu⟩

theorem nine_exists_iff_shifted_source :
    (∃ a : Fin 9 → V,
      (ExecutableJones.expression (SharingSeed38.seed CurrentWindowCarry2011.ports) 0).evalRing
        (fun i => ι (a i)) = 0) ↔
    ∃ u : Fin 14 → V,
      InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)
        (fun j => u j + 1) := by
  constructor
  · intro ha
    obtain ⟨w, hw⟩ := (SharingSeed38CurrentJones.current_nine_iff (V := V)).mp ha
    exact (seed_exists_iff_shifted_source (V := V)).mp
      ⟨w, (internalZero_iff _ _).mpr hw⟩
  · intro hu
    obtain ⟨w, hw⟩ := (seed_exists_iff_shifted_source (V := V)).mpr hu
    apply (SharingSeed38CurrentJones.current_nine_iff (V := V)).mpr
    exact ⟨w, (internalZero_iff _ _).mp hw⟩

end DiophantineConsistency.Norm38CurrentCastFreeIff
#print axioms DiophantineConsistency.Norm38CurrentCastFreeIff.seed_exists_iff_shifted_source
#print axioms DiophantineConsistency.Norm38CurrentCastFreeIff.nine_exists_iff_shifted_source
