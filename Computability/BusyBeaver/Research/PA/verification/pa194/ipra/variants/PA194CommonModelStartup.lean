import PA194CommonStartup

set_option autoImplicit false
set_option maxHeartbeats 0

namespace PA194CommonModelStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine PA194IndexedNumerals

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem lca :
    run (V := V) PA194LCAData.table (58320 : V) =
      (packedCode (24, 1, 152919395647067130113387679226998336721518593) : V) := by
  have length : PA194LCAData.rows.length = 388 := by decide +kernel
  have directions : BinaryDirections PA194LCAData.rows := by
    unfold BinaryDirections
    decide +kernel
  have checked := indexedRun_correct (V := V) PA194LCAData.rows length directions 58320
  rw [PA194CommonStartup.lca] at checked
  simpa [PA194LCAData.table] using checked

theorem m4r :
    run (V := V) PA194M4RData.table (58320 : V) =
      (packedCode (24, 1, 152919395647067130113387679226998336721518593) : V) := by
  have length : PA194M4RData.rows.length = 388 := by decide +kernel
  have directions : BinaryDirections PA194M4RData.rows := by
    unfold BinaryDirections
    decide +kernel
  have checked := indexedRun_correct (V := V) PA194M4RData.rows length directions 58320
  rw [PA194CommonStartup.m4r] at checked
  simpa [PA194M4RData.table] using checked

#print axioms lca
#print axioms m4r
end PA194CommonModelStartup
