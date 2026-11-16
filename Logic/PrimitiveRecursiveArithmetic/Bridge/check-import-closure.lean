import Lean.Elab.ParseImportsFast
import Lean.Util.Path

/-! Run from the repository root with `lake env lean --run`.
The traversal uses Lake's source search path and the same import parser as Lake,
including public, meta, and import-all headers. -/

open Lean

private def renderPath (path : List Name) : String :=
  " → ".intercalate (path.reverse.map toString)

private partial def visit (searchPath : SearchPath) (forbidden : List Name)
    (visited : Std.HashSet Name) (mod : Name) (parents : List Name) : IO (Std.HashSet Name) := do
  let path := mod :: parents
  if parents.contains mod then
    throw <| IO.userError s!"import cycle: {renderPath path}"
  if visited.contains mod then
    return visited
  if forbidden.any (·.isPrefixOf mod) then
    throw <| IO.userError s!"application import in an iPRA core: {renderPath path}"
  let source ← findLean searchPath mod
  let header ← parseImports' (← IO.FS.readFile source) source.toString
  header.imports.foldlM (fun checked imp => visit searchPath forbidden checked imp.module path)
    (visited.insert mod)

private def check (searchPath : SearchPath) (roots forbidden : List Name) : IO Unit := do
  let visited ← roots.foldlM (fun checked mod => visit searchPath forbidden checked mod []) {}
  IO.println s!"Checked {visited.size} source modules from {", ".intercalate (roots.map toString)}."

def main : IO Unit := do
  let searchPath ← getSrcSearchPath
  let applications := [`BusyBeaver, `Diophantine, `ZFCinPA, `BoundedPAConsistency,
    `BoundedZFCConsistency]
  check searchPath [`ConciseIPRA.PR, `IPRADerivations.Core.Semiring, `IPRADerivations.Core.Order]
    (applications ++ [`Foundation, `DiophantineConsistency, `IPRABridge])
  check searchPath [`DiophantineConsistency.IPRAStandardAxioms] (applications ++
    [`DiophantineConsistency.IPRAArithmeticInstantiation,
     `DiophantineConsistency.IPRASuccessorInduction,
     `DiophantineConsistency.IPRASuccessorInductionConverse,
     `DiophantineConsistency.IPRAStandardTheory])
  check searchPath [`IPRABridge.Standard] (applications ++
    [`DiophantineConsistency.IPRAOpenDisjunctionWitness,
     `DiophantineConsistency.IPRADeepEqualityJoin,
     `DiophantineConsistency.IPRAExplicitZFCReduction,
     `DiophantineConsistency.ModelJonesNine])
