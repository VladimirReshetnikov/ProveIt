import PA194HXModelStartup
import PA194DenseStartupComplete
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194HXSharedStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IndexedNumerals

theorem primaryDirections : BinaryDirections PA194Rows.rows := by
  unfold BinaryDirections
  decide +kernel

theorem primaryIndexedSame (n : Nat) :
    indexedRun PA194Rows.rows n = PA194Bounded.run n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change indexedNext PA194Rows.rows (indexedRun PA194Rows.rows n) =
      PA194Bounded.next (PA194Bounded.run n)
    rw [ih]
    rfl

theorem primaryNumericStartup : PA194Bounded.run 58154 =
    PA194Bounded.encodeZip ⟨24,PA194StartupData.seedFrame.l,PA194StartupData.seedFrame.r⟩ := by
  have h := PA194Bounded.zip_run_binding 58154
  rw [PA194Bounded.zip_run_some 58154 _ PA194DenseStartupComplete.startup_exact] at h
  exact h.symm

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem primaryModeledStartup :
    ConPA.Machine.run (V := V) PA194GenericBridge.denseTable (58154 : V) =
      ⟪(24 : V),(1 : V),(PA194Bounded.bits PA194StartupData.seedFrame.r : V)⟫ := by
  have h := indexedRun_correct (V := V) PA194Rows.rows PA194GenericBridge.rowCount primaryDirections 58154
  rw [primaryIndexedSame 58154, primaryNumericStartup, ConPA.Machine.packedCode_cast] at h
  have hl : PA194StartupData.seedFrame.l = [true] := by
    rw [← PA194StartupData.last_eq]
    rfl
  simpa [PA194BModelSteps.tableOld,PA194Bounded.encodeZip,hl,PA194Bounded.bits] using h

/-- The two literal blank runs reach exactly the same physical seed in every
    model of IΣ₁, though at different standard clocks. -/
theorem sharedSeed :
    ConPA.Machine.run (V := V) PA194HXDispatch.table (56134 : V) =
      ConPA.Machine.run (V := V) PA194GenericBridge.denseTable (58154 : V) := by
  rw [PA194HXModelStartup.modeledStartup,primaryModeledStartup]

#print axioms primaryModeledStartup
#print axioms sharedSeed
end models
#print axioms primaryDirections
#print axioms primaryIndexedSame
#print axioms primaryNumericStartup
end PA194HXSharedStartup
