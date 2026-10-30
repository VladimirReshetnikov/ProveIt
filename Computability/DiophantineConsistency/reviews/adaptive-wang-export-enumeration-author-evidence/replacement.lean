import DiophantineConsistency.ArithmeticWangTable
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (n, idx) in env.const2ModIdx.toList do
    if (((env.header.moduleNames).getD idx.toNat Name.anonymous).toString.startsWith "DiophantineConsistency.ArithmeticWangTable") && !isPrivateName n then
      if let some info := env.find? n then
        logInfo m!"EXPORT {n} ::: {reprStr info.type} ::: {reprStr info.levelParams}"
