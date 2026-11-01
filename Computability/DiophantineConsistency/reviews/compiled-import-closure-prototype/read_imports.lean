import Lean.Environment

/-! Read module imports from the main compacted data of each supplied artifact.
This inspects object headers; it does not validate the original compilation. -/
open Lean

def main (args : List String) : IO Unit := do
  let mut index := 0
  for path in args do
    let (data, _region) ← Lean.readModuleData path
    let imports := data.imports.toList.map (fun i => i.module.toString)
    IO.println (String.intercalate "\t" (["OK", toString index, toString data.isModule] ++ imports))
    index := index + 1
