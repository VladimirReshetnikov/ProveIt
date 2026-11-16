import Lean.Environment
import Lean.Util.Path

/-! Read declaration ownership from the selected object files before loading
the bridge. An older object still owns the declaration that current sources
import through the smaller syntax module. -/

open Lean

private def originalOwner (owner declaration replacement : Name) : IO Bool := do
  let file ← findOLean owner
  let (data, _) ← readModuleData file
  if data.constNames.contains declaration then return true
  if data.imports.any (·.module == replacement) then return false
  throw <| IO.userError s!"{file} neither defines {declaration} nor imports {replacement}"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let codes := `DiophantineConsistency.PRAFiniteCodeSyntax
  let legacyCode ← originalOwner `DiophantineConsistency.PRAFiniteFunctionCodes
    `DiophantineConsistency.PRAFiniteFunctionCodes.Code codes
  let legacyGet ← originalOwner `DiophantineConsistency.PRATheory
    `DiophantineConsistency.PRATheory.getCode codes
  unless legacyCode == legacyGet do
    throw <| IO.userError "PRAFiniteFunctionCodes and PRATheory must come from the same syntax split"
  if legacyCode then IO.println "PRAFiniteCodeSyntax PRATheory"
  if ← originalOwner `DiophantineConsistency.IPRAQuantifierFree
      `DiophantineConsistency.IPRAQuantifierFree.OpenI `DiophantineConsistency.IPRAOpenSyntax then
    IO.println "IPRAOpenSyntax IPRAQuantifierFree"
  if ← originalOwner `DiophantineConsistency.IPRAEqualityOnlyReference
      `DiophantineConsistency.IPRAEqualityOnlyReference.language `DiophantineConsistency.IPRAReferenceLanguage then
    IO.println "IPRAReferenceLanguage IPRAEqualityOnlyReference"
