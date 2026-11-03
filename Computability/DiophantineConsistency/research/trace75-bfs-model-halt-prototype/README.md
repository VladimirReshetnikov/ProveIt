# Trace75 direct-BFS graph-to-model-halt client

`Trace75BFSModelHalt.graph_halts` adapts the 80-row model soundness join to trace75.
In any IΣ₁ model, under exact symbolic direct-BFS ports and a positive trace75
zero, it proves a model time t with `first (ArithmeticMachineRun215.run t)=0`.
It composes the represented original-table word with marked-word identification
and machine soundness. The author check passed with tool-observed outer exit 0
and child, Lean and header exits 0. Independent post-audit passed in
`reviews/trace75-bfs-model-halt-result-independent/`.

The runner checks twenty accepted regular client roots, the 1,977-object fresh
union, 80 outside providers and the captured BFS `OldWordIdentification` and
`ArithmeticWangSoundness` subtrees (526 and 135 project objects), including
companions. Read-only preflight and 18 controls passed. The result
`observations/attempt01/result.json` has SHA-256
`f07f6309693b7259e15bd149a14c2da5e96e50c62b5fc82c43ca60d4fa416a4a`;
`observations/outer-attempt01/terminal.json` has SHA-256
`131436b3c3edc596212719a52fb88c0ad62dfa5016fc98ce089610323fc376d3`.
The object `/tmp/trace75-bfs-modelhalt-ipf6iwvw/Trace75BFSModelHalt.olean`
has SHA-256 `f3334e5e331cf93540fc45b92d221c4879bc2c0847068b38d96eae83561f56ae`.
Historical unrebuilt-source, package/dynamic ancestry
and external coefficient-file binding remain outside this check. Even if
checked, this is one model-level direction, not a halt iff or iPRA theorem.
