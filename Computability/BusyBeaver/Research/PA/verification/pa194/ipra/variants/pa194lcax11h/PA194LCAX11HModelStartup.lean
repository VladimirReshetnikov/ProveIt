import PA194LCAX11HRows
import PA194LCAX11HStartupComplete

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PA194LCAX11HModelStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IndexedNumerals PA194LCAX11HData

theorem directions : BinaryDirections rows := by
  unfold BinaryDirections
  decide +kernel

/-- The exact AX11H blank run reaches the primary packed seed in every IΣ₁ model. -/
theorem modeledStartup {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ConPA.Machine.run (V := V) table (57922 : V) =
      ⟪(24 : V), (1 : V), (152919395647067130113387679226998336721518593 : V)⟫ := by
  have h := indexedRun_correct (V := V) rows PA194LCAX11HRows.rowCount directions 57922
  rw [← PA194LCAX11HNumerical.blank 57922, PA194LCAX11HStartup.startup, ConPA.Machine.packedCode_cast] at h
  simpa [table] using h

#print axioms modeledStartup
end PA194LCAX11HModelStartup
