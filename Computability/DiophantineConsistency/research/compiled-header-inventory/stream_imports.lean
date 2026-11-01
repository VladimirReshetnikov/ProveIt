import Lean.Environment

/-! Read one compiled object header per input line. This is an object-header
survey, not a runtime trace or a proof of source-to-object provenance. -/
open Lean

private def describe (data : ModuleData) : String :=
  toString data.isModule ++ ":" ++ String.intercalate "," (data.imports.toList.map (fun i => i.module.toString))

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let fields := ((line.dropSuffix "\n").toString.splitOn "\t")
    let [mainFile, serverFile, privateFile, irFile] := fields
      | throw <| IO.userError "expected four tab-separated artifact paths"
    let isModule ← do
      let (data, _region) ← Lean.readModuleData mainFile
      pure data.isModule
    if isModule && (serverFile == "-" || privateFile == "-") then
      throw <| IO.userError "module object parts missing"
    if !isModule && (serverFile != "-" || privateFile != "-") then
      throw <| IO.userError "unexpected parts on non-module object"
    let filenames := if isModule then #[mainFile, serverFile, privateFile] else #[mainFile]
    let parts ← Lean.readModuleDataParts (filenames.map System.FilePath.mk)
    let descriptions := parts.toList.map (fun part => describe part.1)
    let (mainDescription, serverDescription, privateDescription) ←
      if isModule then do
        let [a, b, c] := descriptions | throw <| IO.userError "unexpected module part count"
        pure (a, b, c)
      else do
        let [a] := descriptions | throw <| IO.userError "unexpected object part count"
        pure (a, "-", "-")
    let irDescription ← if irFile == "-" then pure "-" else do
      let (data, _region) ← Lean.readModuleData irFile
      pure (describe data)
    output.putStr (String.intercalate "\t" ["OK", mainDescription, serverDescription, privateDescription, irDescription] ++ "\n")
    output.flush
