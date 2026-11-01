import Lean
open Lean
unsafe def main (args : List String) : IO Unit := do
  for path in args do
    try
      let (data, region) ← readModuleData (System.FilePath.mk path)
      let names := data.imports.toList.map (fun i => toString i.module)
      IO.println s!"{path}\t{String.intercalate "," names}"
      region.free
    catch e => IO.eprintln s!"ERROR {path}: {e}"
