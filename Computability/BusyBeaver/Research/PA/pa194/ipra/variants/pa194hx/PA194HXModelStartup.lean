import PA194IndexedNumerals
import PA194HXZipBridge
import PA194HXDenseStartupComplete
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
namespace PA194HXModelStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IndexedNumerals PA194HXZipBridge

theorem directions : BinaryDirections PA194HXRows.rows := by
  unfold BinaryDirections
  decide +kernel

theorem indexed_same (n : Nat) :
    indexedRun PA194HXRows.rows n = PA194HXZipBridge.run n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change indexedNext PA194HXRows.rows (indexedRun PA194HXRows.rows n) =
      PA194HXZipBridge.next (PA194HXZipBridge.run n)
    rw [ih]
    rfl

theorem numericStartup :
    PA194HXZipBridge.run 56134 =
      encodeZip ⟨24,PA194StartupData.seedFrame.l,PA194StartupData.seedFrame.r⟩ := by
  have h := zip_run_binding 56134
  rw [zip_run_some 56134 _ PA194HXDenseStartupComplete.startup_exact] at h
  exact h.symm

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- At the standard clock 56,134 the exact HX table reaches the primary
    physical source-seed tape in every model of IΣ₁. -/
theorem modeledStartup :
    ConPA.Machine.run (V := V) PA194HXDispatch.table (56134 : V) =
      ⟪(24 : V),(1 : V),(PA194Bounded.bits PA194StartupData.seedFrame.r : V)⟫ := by
  have h := indexedRun_correct (V := V) PA194HXRows.rows PA194HXDispatch.rowCount directions 56134
  rw [indexed_same 56134, numericStartup, ConPA.Machine.packedCode_cast] at h
  have hl : PA194StartupData.seedFrame.l = [true] := by
    rw [← PA194StartupData.last_eq]
    rfl
  simpa [PA194HXDispatch.table,encodeZip,hl,PA194Bounded.bits] using h

#print axioms modeledStartup
end models
#print axioms indexed_same
#print axioms directions
#print axioms numericStartup
end PA194HXModelStartup
