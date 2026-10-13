import GowersSzemeredi.Final
import ImportGraph.Imports.RequiredModules

set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : NameSet := (#[
    ``LeanProofs.GowersSzemeredi.theorem_18_2_explicit,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_explicit,
    ``LeanProofs.GowersSzemeredi.theorem_1_2_explicit,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_explicit ] : Array Name).foldl
      (fun names name => names.insert name) {}
  let required ← liftCoreM <| roots.transitivelyUsedConstants
  for name in required do
    if let some module := env.getModuleFor? name then
      if (`GowersSzemeredi).isPrefixOf module || (`OAI).isPrefixOf module then
        liftIO <| IO.println s!"{module}\t{name}"
