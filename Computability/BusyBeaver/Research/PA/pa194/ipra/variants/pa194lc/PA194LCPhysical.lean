import PA194LCRows
import PA194LCChecks

set_option autoImplicit false

namespace PA194LCPhysical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.Runtime
open ConPA.Machine ConPA.Machine.Compressed
open PA194LCData PA194LCChecks

theorem rootControl : denseControl 84 = 24 := by decide +kernel
theorem haltControl : denseControl 254 = 194 := by decide +kernel
theorem rowCount : rows.length = 388 := by decide +kernel

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable abbrev root (gap : V) (box : BoxSt → V) (i : Nat)
    (extra : Nat := 0) (effect : Eff := .none) : V :=
  PA194SourceContracts.root denseControl path gap box i extra effect

theorem contract_sound (gap : V) {br : Branch} {box : BoxSt → V}
    (boxes : BoxAgreement table denseControl br box) (i j extra fuel : Nat) (effect : Eff)
    (cert : contract br i j extra fuel effect = true) :
    Reach1 table (root gap box i) (root gap box j extra effect) :=
  PA194SourceContracts.contract_sound PA194LCRows.rowAgreement path gap boxes i j extra fuel effect cert

theorem halt_sound (gap : V) {box : BoxSt → V}
    (boxes : BoxAgreement table denseControl none box) (i fuel : Nat)
    (cert : haltContract i fuel = true) :
    ∃ final, Reach1 table (root gap box i) final ∧ π₁ final = (194 : V) :=
  PA194SourceContracts.halt_sound PA194LCRows.rowAgreement path haltControl gap boxes i fuel cert

#print axioms contract_sound
#print axioms halt_sound
end models
end PA194LCPhysical
