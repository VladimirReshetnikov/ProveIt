import PA194VariantPackedStep
import PAVariantADInstance
import PA194ADStartupModel
import PA194UnaryRecursionGraph

/-! The explicit packed AD clock represents the same run as the generic
arithmetic machine in all covered models. -/

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace PA194ADGenericRun
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194HalfDiv PackedRootModel

abbrev table := PA194BModelSteps.table PA194ADTable.adRows

theorem rowCount : PA194ADTable.adRows.length = 388 := by decide +kernel

theorem stepCode_eq :
    PA194VariantPackedStep.stepCode PA194ADTable.adRows = PA194ADClock.encodedStep := by
  simp only [PA194VariantPackedStep.stepCode, PA194ADClock.encodedStep,
    PAVariantADInstance.nextQ_eq, PAVariantADInstance.nextL_eq, PAVariantADInstance.nextR_eq]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem clock_run (t : M) : F PA194ADClock.clock (fun _ => t) = ConPA.Machine.run table t := by
  have hz : (ConPA.Machine.blueprint table).zero.val.Evalb (M := M) ![F (Code.zero 0) Fin.elim0] := by
    simp [ConPA.Machine.blueprint]
    rfl
  have hs (i z : M) : (ConPA.Machine.blueprint table).succ.val.Evalb (M := M)
      ![F PA194ADClock.clockStep ![i,z],z,i] := by
    have hstep : F PA194ADClock.clockStep ![i,z] = F PA194ADClock.encodedStep (fun _ => z) := by
      simp [PA194ADClock.clockStep, modelUnary, modelProjection]
    rw [hstep, ←stepCode_eq, PA194VariantPackedStep.modelStep _ rowCount]
    simp [ConPA.Machine.blueprint, ConPA.Machine.stepDef_iff]
  have h := PA194UnaryRecursionGraph.modelResult_eq (M := M) (ConPA.Machine.blueprint table)
    (ConPA.Machine.construction table) (Code.zero 0) PA194ADClock.clockStep hz hs t
  have he : (Fin.elim0 : Fin 0 → M) = ![] := Subsingleton.elim _ _
  simpa only [PRAHistoryIterator.valueCode, PA194ADClock.clock, ConPA.Machine.run, he] using h

/-- The arithmetic AD run reaches the common source seed at its checked
startup clock, including in nonstandard IΣ₁ reducts of PRA models. -/
theorem startup_seed :
    ConPA.Machine.run table (58122 : M) =
      ⟪(24 : M),(1 : M),(PA194Bounded.bits PA194StartupData.seedFrame.r : M)⟫ := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := PA194ADStartupModel.startup_seed (M := M)
  rw [clock_run] at h
  simpa only [modelNumeralCast, Nat.cast_ofNat, Nat.cast_one, modelPairCode] using h

#print axioms clock_run
#print axioms startup_seed
end models
end PA194ADGenericRun
