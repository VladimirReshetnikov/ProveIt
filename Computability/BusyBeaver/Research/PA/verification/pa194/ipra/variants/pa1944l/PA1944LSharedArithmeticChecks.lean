import Lean.Environment
import Lean.Util.FoldConsts
import Lean.Util.Path

/-! Audit the arithmetic used by the literal endpoint in the current
provider environment. This check follows proof values. -/

set_option autoImplicit false

open Lean

private def proofPath (decls : Std.HashMap Name ConstantInfo) (source target : Name) : Option (List Name) := Id.run do
  let mut visited : Std.HashSet Name := {source}
  let mut pending : Array (Name × List Name) := #[(source, [])]
  let mut index := 0
  while index < pending.size do
    let (name, parents) := pending[index]!
    index := index + 1
    if name == target then return some (name :: parents).reverse
    let some info := decls[name]? | continue
    let some value := info.value? (allowOpaque := true) | continue
    for dependency in value.getUsedConstants do
      if !visited.contains dependency then
        visited := visited.insert dependency
        pending := pending.push (dependency, name :: parents)
  return none

private def proofDeclarations : IO (Std.HashMap Name ConstantInfo) := do
  let modules := #[
    `PA1944LFinal, `PA1944LNative, `PA194ControllerNative, `PA194NativeLiteralFinal,
    `PA194NativeCalibratedEndpoint, `PA194ConditionalDenseEndpoint,
    `ConPAISigma1Directions, `ConPAISigma1Transfer,
    `DiophantineConsistency.IPRABoundedInduction, `DiophantineConsistency.IPRABoundedSelector,
    `DiophantineConsistency.IPRABoundedLogic, `DiophantineConsistency.IPRABoundedChild,
    `DiophantineConsistency.IPRASelectorSearchBinding,
    `DiophantineConsistency.IPRANativeEqualityDecidable,
    `DiophantineConsistency.IPRADifferenceStepClosure,
    `DiophantineConsistency.IPRADifferenceSuccLogic, `DiophantineConsistency.IPRADifferenceSuccEq,
    `DiophantineConsistency.IPRASubSuccSelfNonzero, `IPRADerivations.Core.Order,
    `IPRABridge.BoundedSearch, `IPRADerivations.Core.SearchParameters]
  let mut decls := {}
  for mod in modules do
    let file ← findOLean mod
    let parts ← (#[file, Lean.OLeanLevel.server.adjustFileName file,
      Lean.OLeanLevel.private.adjustFileName file]).filterM (fun path => do path.pathExists)
    let moduleData ← readModuleDataParts parts
    for (data, _) in moduleData do
      for info in data.constants do
        decls := decls.insert info.name info
  return decls

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let decls ← proofDeclarations
  let endpoint := `PA1944LFinal.consistency_iff_literal_nonhalt
  let paths := #[
    (`DiophantineConsistency.IPRASubSuccSelfNonzero.native, `LeanProofs.IPRA.not_succ_le_self),
    (`DiophantineConsistency.IPRABoundedSelector.selectorOpen, `LeanProofs.IPRA.Search.Finite.search_found)]
  for (helper, shared) in paths do
    let some usePath := proofPath decls endpoint helper
      | throw <| IO.userError s!"{endpoint} does not use {helper}"
    let some arithmeticPath := proofPath decls helper shared
      | throw <| IO.userError s!"{helper} does not use {shared}"
    IO.println (" → ".intercalate ((usePath ++ arithmeticPath.drop 1).map toString))
