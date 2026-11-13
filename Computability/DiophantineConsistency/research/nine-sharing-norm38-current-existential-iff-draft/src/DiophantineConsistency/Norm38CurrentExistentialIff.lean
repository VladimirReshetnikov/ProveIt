import DiophantineConsistency.Norm38CurrentSourceToSeed
import DiophantineConsistency.Norm38CurrentSeedSource
import DiophantineConsistency.SharingSeed38CurrentJones

/-! Source-only composition; a later concrete wrapper must discharge hp. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38CurrentExistentialIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_exists_iff_shifted_source (ports : Fin 4 → V)
    (hp : ∀ j, ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (ports j)) :
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
    exact ⟨SharingForward38.witnessCoordinates ports u,
      Norm38CurrentSourceToSeed.source_zero_implies_seed_zero ports u hp hu⟩

theorem nine_exists_iff_shifted_source (ports : Fin 4 → V)
    (hp : ∀ j, ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (ports j)) :
    (∃ a : Fin 9 → V,
      (ExecutableJones.expression (SharingSeed38.seed CurrentWindowCarry2011.ports) 0).evalRing
        (fun i => ι (a i)) = 0) ↔
    ∃ u : Fin 14 → V,
      InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)
        (fun j => u j + 1) := by
  constructor
  · intro ha
    obtain ⟨w, hw⟩ := (SharingSeed38CurrentJones.current_nine_iff (V := V)).mp ha
    exact (seed_exists_iff_shifted_source ports hp).mp
      ⟨w, (internalZero_iff _ _).mpr hw⟩
  · intro hu
    obtain ⟨w, hw⟩ := (seed_exists_iff_shifted_source ports hp).mpr hu
    apply (SharingSeed38CurrentJones.current_nine_iff (V := V)).mpr
    exact ⟨w, (internalZero_iff _ _).mp hw⟩

end DiophantineConsistency.Norm38CurrentExistentialIff
#print axioms DiophantineConsistency.Norm38CurrentExistentialIff.seed_exists_iff_shifted_source
#print axioms DiophantineConsistency.Norm38CurrentExistentialIff.nine_exists_iff_shifted_source
