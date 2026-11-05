import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The sum-of-squares theorem supplies a zero at each indexed slot. -/
theorem each_slot_zero (p : Fin 4 → ℤ) (w : Fin 38 → V)
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w))
    (i : Fin 29) : (residualAt p i).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) = 0 := by
  have all := (SharingNormSquares.seed_zero_iff_residuals p (Fin.cons (1 : V) w)).mp hz
  have hm : residualAt p i ∈ residuals p := List.get_mem _ _
  exact ((internalZero_iff _ _).mp (all _ hm))


end DiophantineConsistency.Norm38SlotExtraction
