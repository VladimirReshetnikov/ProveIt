import DiophantineConsistency.Norm38Slots00
import DiophantineConsistency.Norm38Slots01
import DiophantineConsistency.Norm38Slots02
import DiophantineConsistency.Norm38Slots03
import DiophantineConsistency.Norm38Slots04
import DiophantineConsistency.Norm38Slots05
import DiophantineConsistency.Norm38Slots06
import DiophantineConsistency.Norm38Slots07
import DiophantineConsistency.Norm38Slots08
import DiophantineConsistency.Norm38Slots09
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
  exact (internalZero_iff.mp (all _ hm))

/-- Proposed extraction from the 29 literal equalities to the static graph
constraints. It is not a source-expression identification or model bridge. -/
theorem seed_zero_static (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    NormAssignment38.gatesHold ι ports w ∧ NormAssignment38.fiveNorms ι ports w := by
  have h00 := each_slot_zero p w hz 0
  rw [slot00 p ports w hp] at h00
  have h01 := each_slot_zero p w hz 1
  rw [slot01 p ports w hp] at h01
  have h02 := each_slot_zero p w hz 2
  rw [slot02 p ports w hp] at h02
  have h03 := each_slot_zero p w hz 3
  rw [slot03 p ports w hp] at h03
  have h04 := each_slot_zero p w hz 4
  rw [slot04 p ports w hp] at h04
  have h05 := each_slot_zero p w hz 5
  rw [slot05 p ports w hp] at h05
  have h06 := each_slot_zero p w hz 6
  rw [slot06 p ports w hp] at h06
  have h07 := each_slot_zero p w hz 7
  rw [slot07 p ports w hp] at h07
  have h08 := each_slot_zero p w hz 8
  rw [slot08 p ports w hp] at h08
  have h09 := each_slot_zero p w hz 9
  rw [slot09 p ports w hp] at h09
  have h10 := each_slot_zero p w hz 10
  rw [slot10 p ports w hp] at h10
  have h11 := each_slot_zero p w hz 11
  rw [slot11 p ports w hp] at h11
  have h12 := each_slot_zero p w hz 12
  rw [slot12 p ports w hp] at h12
  have h13 := each_slot_zero p w hz 13
  rw [slot13 p ports w hp] at h13
  have h14 := each_slot_zero p w hz 14
  rw [slot14 p ports w hp] at h14
  have h15 := each_slot_zero p w hz 15
  rw [slot15 p ports w hp] at h15
  have h16 := each_slot_zero p w hz 16
  rw [slot16 p ports w hp] at h16
  have h17 := each_slot_zero p w hz 17
  rw [slot17 p ports w hp] at h17
  have h18 := each_slot_zero p w hz 18
  rw [slot18 p ports w hp] at h18
  have h19 := each_slot_zero p w hz 19
  rw [slot19 p ports w hp] at h19
  have h20 := each_slot_zero p w hz 20
  rw [slot20 p ports w hp] at h20
  have h21 := each_slot_zero p w hz 21
  rw [slot21 p ports w hp] at h21
  have h22 := each_slot_zero p w hz 22
  rw [slot22 p ports w hp] at h22
  have h23 := each_slot_zero p w hz 23
  rw [slot23 p ports w hp] at h23
  have h24 := each_slot_zero p w hz 24
  rw [slot24 p ports w hp] at h24
  have h25 := each_slot_zero p w hz 25
  rw [slot25 p ports w hp] at h25
  have h26 := each_slot_zero p w hz 26
  rw [slot26 p ports w hp] at h26
  have h27 := each_slot_zero p w hz 27
  rw [slot27 p ports w hp] at h27
  have h28 := each_slot_zero p w hz 28
  rw [slot28 p ports w hp] at h28
  constructor
  · unfold NormAssignment38.gatesHold
    simp only [NormAssignment38.gates, List.mem_cons, forall_eq_or_imp]
    repeat' constructor
    all_goals simp_all [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute]
  · unfold NormAssignment38.fiveNorms
    exact ⟨sub_eq_zero.mp h16, sub_eq_zero.mp h11, sub_eq_zero.mp h27, sub_eq_zero.mp h17, sub_eq_zero.mp h28⟩

-- Remaining: compile and repair these statements; prove the static-to-source
-- topological evaluation, fixed-port casts, forward witness construction,
-- Jones instantiation and consistency transfer.

end DiophantineConsistency.Norm38SlotExtraction
