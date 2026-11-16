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

private def report (searchPath : SearchPath) (root : Name) : IO Unit := do
  let source ← findLean searchPath root
  let header ← parseImports' (← IO.FS.readFile source) source.toString
  let visited ← visit searchPath [] {} root []
  let imports := visited.toArray.filter (· != root)
  let counts := imports.foldl (init := ({} : Std.HashMap Name Nat)) fun acc mod =>
    let ns := mod.getRoot
    acc.insert ns (acc.getD ns 0 + 1)
  IO.println s!"{root}: {header.imports.size} header entries, {imports.size} transitive imports"
  IO.println s!"  source: {source}"
  let direct := header.imports.toList.map (fun imp => toString imp.module)
  IO.println s!"  direct: {", ".intercalate direct}"
  for (ns, count) in counts.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    IO.println s!"  {ns}: {count}"

private def checkPortableLayers (searchPath : SearchPath) : IO Unit := do
  let applications := [`BusyBeaver, `Diophantine, `ZFCinPA, `BoundedPAConsistency,
    `BoundedZFCConsistency]
  check searchPath [`ConciseIPRA.PR, `IPRADerivations]
    (applications ++ [`Foundation, `DiophantineConsistency, `IPRABridge])
  check searchPath [`DiophantineConsistency.PRAFiniteCodeSyntax]
    (applications ++ [`Foundation, `Mathlib.Computability.Primrec,
      `DiophantineConsistency.PRAFiniteFunctionCodes, `DiophantineConsistency.PRAFunctionCodes])
  check searchPath [`IPRABridge.Syntax] (applications ++
    [`Foundation.FirstOrder.Intuitionistic.Deduction,
     `Foundation.FirstOrder.NegationTranslation.GoedelGentzen,
     `DiophantineConsistency.PRATheory, `DiophantineConsistency.PRALanguage,
     `DiophantineConsistency.PRAFunctionCodes, `DiophantineConsistency.IPRAEqualityOnlyReference,
     `DiophantineConsistency.IPRAQuantifierFree])
  check searchPath [`DiophantineConsistency.IPRAStandardAxioms] (applications ++
    [`DiophantineConsistency.IPRAArithmeticInstantiation,
     `DiophantineConsistency.IPRASuccessorInduction,
     `DiophantineConsistency.IPRASuccessorInductionConverse,
     `DiophantineConsistency.IPRAStandardTheory])
  check searchPath [`IPRABridge, `IPRABridge.OrderSymbols, `IPRABridge.ComparisonBits] (applications ++
    [`DiophantineConsistency.IPRAOpenDisjunctionWitness,
     `DiophantineConsistency.IPRADeepEqualityJoin,
     `DiophantineConsistency.IPRAExplicitZFCReduction,
     `DiophantineConsistency.ModelJonesNine])

def main (args : List String) : IO Unit := do
  let searchPath ← getSrcSearchPath
  match args with
  | [] => checkPortableLayers searchPath
  | "--inventory" :: first :: rest =>
    for root in first :: rest do
      report searchPath root.toName
  | _ => throw <| IO.userError "usage: check-import-closure.lean [--inventory MODULE ...]"
