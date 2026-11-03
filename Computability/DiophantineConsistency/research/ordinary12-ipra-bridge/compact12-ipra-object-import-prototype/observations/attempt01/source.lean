import Lean.Environment

/-! Read stored direct-import names from one Lean object. -/
open Lean

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let (data, _region) ← readModuleData (System.FilePath.mk path)
    IO.println s!"BEGIN {path}"
    for imp in data.imports do
      IO.println s!"IMPORT {imp.module}"
    IO.println "END"
  | _ => throw (IO.userError "expected exactly one .olean path")
