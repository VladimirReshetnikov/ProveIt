import PA194LCBData
import PA194SourceContracts

set_option autoImplicit false

namespace PA194LCBChecks
open M6.Source
open PA194LCBData

abbrev contract := PA194SourceContracts.contract machine path
abbrev haltContract := PA194SourceContracts.haltContract machine path
abbrev checkInstruction := PA194SourceContracts.checkInstruction machine path
abbrev checkAt := PA194SourceContracts.checkAt machine path codeAt
abbrev blockCheck := PA194SourceContracts.blockCheck checkAt

theorem block_sound {base count i : Nat} (h : blockCheck base count = true)
    (lo : base ≤ i) (hi : i < base + count) : checkAt i = true :=
  PA194SourceContracts.block_sound h lo hi

theorem checked_at (i : Nat) (h : checkAt i = true) :
    ∃ code, M6.Source.resolveAt PA194SourceProgram.sites i = some code ∧ checkInstruction i code = true :=
  PA194SourceContracts.checked_at machine path codeAt i h

#print axioms checked_at
end PA194LCBChecks
