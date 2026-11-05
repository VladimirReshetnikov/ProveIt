import DiophantineConsistency.Norm38EachSlot
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
namespace DiophantineConsistency.Norm38Forward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Candidate reverse use of the literal slot identities: all static gate and
norm constraints make every squared residual zero. -/
theorem static_implies_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hg : NormAssignment38.gatesHold ι ports w)
    (hn : NormAssignment38.fiveNorms ι ports w) :
    InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w) := by
  unfold NormAssignment38.gatesHold at hg
  unfold NormAssignment38.fiveNorms at hn
  rcases hn with ⟨hn0,hn1,hna,hnt,hns⟩
  have gate_23 := hg ⟨23, 22, 22, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_24 := hg ⟨24, 23, 22, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_25 := hg ⟨25, 8, 22, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_26 := hg ⟨26, 7, 24, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_27 := hg ⟨27, 25, 26, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_29 := hg ⟨29, 28, 26, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_30 := hg ⟨30, 27, 29, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_36 := hg ⟨36, 35, 34, GateOp.add⟩ (by simp [NormAssignment38.gates])
  have gate_40 := hg ⟨40, 38, 39, GateOp.add⟩ (by simp [NormAssignment38.gates])
  have gate_41 := hg ⟨41, 31, 31, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_42 := hg ⟨42, 36, 41, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_48 := hg ⟨48, 47, 2, GateOp.add⟩ (by simp [NormAssignment38.gates])
  have gate_57 := hg ⟨57, 56, 54, GateOp.sub⟩ (by simp [NormAssignment38.gates])
  have gate_67 := hg ⟨67, 4, 4, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_69 := hg ⟨69, 68, 54, GateOp.sub⟩ (by simp [NormAssignment38.gates])
  have gate_71 := hg ⟨71, 70, 31, GateOp.sub⟩ (by simp [NormAssignment38.gates])
  have gate_72 := hg ⟨72, 5, 42, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_73 := hg ⟨73, 72, 72, GateOp.mul⟩ (by simp [NormAssignment38.gates])
  have gate_76 := hg ⟨76, 74, 75, GateOp.sub⟩ (by simp [NormAssignment38.gates])
  have hz00 : InternalZero (residualAt p 0) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot00 p ports w hp]
    exact gate_23.1
  have hz01 : InternalZero (residualAt p 1) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot01 p ports w hp]
    exact gate_24.1
  have hz02 : InternalZero (residualAt p 2) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot02 p ports w hp]
    exact gate_25.1
  have hz03 : InternalZero (residualAt p 3) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot03 p ports w hp]
    exact gate_26.1
  have hz04 : InternalZero (residualAt p 4) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot04 p ports w hp]
    exact gate_27.1
  have hz05 : InternalZero (residualAt p 5) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot05 p ports w hp]
    exact gate_29.1
  have hz06 : InternalZero (residualAt p 6) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot06 p ports w hp]
    exact gate_30.1
  have hz07 : InternalZero (residualAt p 7) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot07 p ports w hp]
    exact gate_36.1
  have hz08 : InternalZero (residualAt p 8) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot08 p ports w hp]
    exact gate_40.1
  have hz09 : InternalZero (residualAt p 9) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot09 p ports w hp]
    exact gate_41.1
  have hz10 : InternalZero (residualAt p 10) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot10 p ports w hp]
    exact gate_42.1
  have hz11 : InternalZero (residualAt p 11) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot11 p ports w hp]
    exact sub_eq_zero.mpr hn1
  have hz12 : InternalZero (residualAt p 12) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot12 p ports w hp]
    exact gate_48.1
  have hz13 : InternalZero (residualAt p 13) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot13 p ports w hp]
    exact gate_48.2
  have hz14 : InternalZero (residualAt p 14) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot14 p ports w hp]
    exact gate_57.1
  have hz15 : InternalZero (residualAt p 15) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot15 p ports w hp]
    exact gate_57.2
  have hz16 : InternalZero (residualAt p 16) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot16 p ports w hp]
    exact sub_eq_zero.mpr hn0
  have hz17 : InternalZero (residualAt p 17) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot17 p ports w hp]
    exact sub_eq_zero.mpr hnt
  have hz18 : InternalZero (residualAt p 18) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot18 p ports w hp]
    exact gate_67.1
  have hz19 : InternalZero (residualAt p 19) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot19 p ports w hp]
    exact gate_69.1
  have hz20 : InternalZero (residualAt p 20) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot20 p ports w hp]
    exact gate_69.2
  have hz21 : InternalZero (residualAt p 21) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot21 p ports w hp]
    exact gate_71.1
  have hz22 : InternalZero (residualAt p 22) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot22 p ports w hp]
    exact gate_71.2
  have hz23 : InternalZero (residualAt p 23) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot23 p ports w hp]
    exact gate_72.1
  have hz24 : InternalZero (residualAt p 24) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot24 p ports w hp]
    exact gate_73.1
  have hz25 : InternalZero (residualAt p 25) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot25 p ports w hp]
    exact gate_76.1
  have hz26 : InternalZero (residualAt p 26) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot26 p ports w hp]
    exact gate_76.2
  have hz27 : InternalZero (residualAt p 27) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot27 p ports w hp]
    exact sub_eq_zero.mpr hna
  have hz28 : InternalZero (residualAt p 28) (Fin.cons (1 : V) w) := by
    rw [internalZero_iff, slot28 p ports w hp]
    exact sub_eq_zero.mpr hns
  have all (i : Fin 29) : InternalZero (residualAt p i) (Fin.cons (1 : V) w) := by
    fin_cases i <;> assumption
  apply (SharingNormSquares.seed_zero_iff_residuals p (Fin.cons (1 : V) w)).mpr
  intro e he
  obtain ⟨j,hj⟩ := List.get_of_mem he
  let i : Fin 29 := ⟨j.val, by simpa [residuals, SharingSeed38.remainingResiduals] using j.isLt⟩
  have hi := all i
  have hget : residualAt p i = e := by
    change (residuals p).get ⟨j.val, _⟩ = e
    exact hj
  simpa only [hget] using hi


end DiophantineConsistency.Norm38Forward
