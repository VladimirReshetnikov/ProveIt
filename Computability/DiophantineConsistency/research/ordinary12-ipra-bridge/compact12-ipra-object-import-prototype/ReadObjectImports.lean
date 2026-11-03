import Lean.Environment

/-! Read stored direct-import names from a bounded batch of Lean objects. -/
open Lean

def main (args : List String) : IO Unit := do
  if args.isEmpty then throw (IO.userError "expected one or more .olean paths")
  for path in args do
    let (data, _region) ← readModuleData (System.FilePath.mk path)
    IO.println s!"BEGIN {path}"
    for imp in data.imports do
      IO.println s!"IMPORT {imp.module}"
    IO.println "END"
