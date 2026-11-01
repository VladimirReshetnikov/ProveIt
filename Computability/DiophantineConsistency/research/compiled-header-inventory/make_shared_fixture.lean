import Lean.Environment

/-! Save the same ModuleData object as three ordered compacted parts. The
compactor may share references from later parts into earlier regions. -/
open Lean

unsafe def main (args : List String) : IO Unit := do
  let [base] := args | throw <| IO.userError "expected output stem"
  let shared : ModuleData := {
    isModule := true
    imports := #[{module := `Synthetic.Dependency}]
    constNames := #[`Synthetic.Shared]
    constants := #[]
    extraConstNames := #[]
    entries := #[]
  }
  Lean.saveModuleDataParts `Synthetic.Shared #[
    (System.FilePath.mk (base ++ ".olean"), shared),
    (System.FilePath.mk (base ++ ".olean.server"), shared),
    (System.FilePath.mk (base ++ ".olean.private"), shared)]
  let parts ← Lean.readModuleDataParts #[System.FilePath.mk (base ++ ".olean"),
    System.FilePath.mk (base ++ ".olean.server"), System.FilePath.mk (base ++ ".olean.private")]
  let [mainPart, serverPart, privatePart] := parts.toList
    | throw <| IO.userError "unexpected part count"
  unless ptrEq mainPart.1.imports serverPart.1.imports && ptrEq mainPart.1.imports privatePart.1.imports do
    throw <| IO.userError "fixture does not share its imported-name array across regions"
  IO.println "SHARED_REGION_CONFIRMED"
