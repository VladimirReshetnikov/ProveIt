import PA194SeedWidthGrowth
import Lean.Util.FoldConsts
open Lean Elab Command
set_option maxRecDepth 65536
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let mut todo : Array Name := #[`PA194SeedWidthGrowth.blankReachesGrowingLoop]
  let mut seen : Std.HashSet Name := {}
  let mut hits : Array Name := #[]
  let mut missing : Array Name := #[]
  while let some n := todo.back? do
    todo := todo.pop
    unless seen.contains n do
      seen := seen.insert n
      if n.toString.startsWith "PA194ActualLoopExactStep." then hits := hits.push n
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
      else
        missing := missing.push n
  logInfo m!"PROOF_DEPENDENCIES visited={seen.size}, exactStep={hits}, missing={missing}"
