import DiophantineConsistency.PRACurrentConsistencyEndpoint
open Lean Elab Command

/-! Exact dependency cone of endpoint theorems, for route-shortening audits.

Run from the repository root, once the imported endpoints are built:
`lake env lean Computability/DiophantineConsistency/research/endpoint-cone/ConeExact.lean`.
It walks `ConstantInfo.getUsedConstantsAsSet` from the roots below through every
project constant, then writes `out/cone_exact.tsv` (reached and total constants per
project module) and `out/module_uses.tsv` (exact direct module-to-module usage by
constants). Elaboration-only dependencies (tactic and macro definitions, notation)
leave no trace in terms, so a proposed import cut must still be compiled. Edit
the import and `roots` to audit another endpoint. -/

/-- Exact constant cone of the endpoint theorems, restricted to project modules. -/
def projectPrefixes : List String :=
  ["DiophantineConsistency", "ZFCinPA", "BusyBeaver", "BoundedZFCConsistency", "BoundedPAConsistency",
   "Diophantine", "PAHF"]

def outDir : String := "Computability/DiophantineConsistency/research/endpoint-cone/out/"

run_cmd do
  let env ← getEnv
  let isProject (m : Name) : Bool := projectPrefixes.any (fun p => m.getRoot.toString == p)
  let modOf (c : Name) : Option Name := (env.getModuleIdxFor? c).bind (fun i => env.header.moduleNames[i.toNat]?)
  let roots : List Name :=
    [`DiophantineConsistency.HACurrentEquation2011.ha_current_iff_consistency,
     `DiophantineConsistency.PRACurrentConsistencyEndpoint.pra_current_iff_consistency]
  let mut seen : NameHashSet := {}
  let mut stack : Array Name := roots.toArray
  while _h : stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    for d in ci.getUsedConstantsAsSet do
      if !seen.contains d then
        match modOf d with
        | some m => if isProject m then stack := stack.push d
        | none => stack := stack.push d
  let mut tot : Std.HashMap Name Nat := {}
  let mut hit : Std.HashMap Name Nat := {}
  let mut uses : Std.HashMap Name NameSet := {}
  for (c, ci) in env.constants.map₁.toList do
    if let some a := modOf c then
      if isProject a then
        tot := tot.insert a (tot.getD a 0 + 1)
        if seen.contains c then hit := hit.insert a (hit.getD a 0 + 1)
        for d in ci.getUsedConstantsAsSet do
          if let some b := modOf d then
            if isProject b && b != a then
              uses := uses.insert a ((uses.getD a {}).insert b)
  let mut lines : Array String := #[]
  for (m, n) in tot.toList do
    lines := lines.push s!"{hit.getD m 0}\t{n}\t{m}"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir ++ "cone_exact.tsv") (String.intercalate "\n" lines.toList)
  let mut ul : Array String := #[]
  for (a, bs) in uses.toList do
    for b in bs do ul := ul.push s!"{a}\t{b}"
  IO.FS.writeFile (outDir ++ "module_uses.tsv") (String.intercalate "\n" ul.toList)
  logInfo m!"reached {seen.size} constants; {tot.size} project modules; {ul.size} usage edges"
