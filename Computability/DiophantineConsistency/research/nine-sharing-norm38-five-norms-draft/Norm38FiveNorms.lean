import DiophantineConsistency.Norm38EachSlot
import DiophantineConsistency.Norm38Slots03
import DiophantineConsistency.Norm38Slots05
import DiophantineConsistency.Norm38Slots09

/-! UNCOMPILED draft: seed-zero implies five static norm targets only. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_fiveNorms (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    NormAssignment38.fiveNorms ι ports w := by
  have h11 := each_slot_zero p w hz 11
  rw [slot11 p ports w hp] at h11
  have h16 := each_slot_zero p w hz 16
  rw [slot16 p ports w hp] at h16
  have h17 := each_slot_zero p w hz 17
  rw [slot17 p ports w hp] at h17
  have h27 := each_slot_zero p w hz 27
  rw [slot27 p ports w hp] at h27
  have h28 := each_slot_zero p w hz 28
  rw [slot28 p ports w hp] at h28
  unfold NormAssignment38.fiveNorms
  exact ⟨sub_eq_zero.mp h16, sub_eq_zero.mp h11, sub_eq_zero.mp h27,
    sub_eq_zero.mp h17, sub_eq_zero.mp h28⟩
end DiophantineConsistency.Norm38SlotExtraction
