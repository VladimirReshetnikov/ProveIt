# Final assembly runner preparation

The held template and its parent-free controls were independently reviewed
in [the template review](../../reviews/trace75-bfs-ipra-final-template-independent/README.md)
and [the outer-wrapper review](../../reviews/trace75-bfs-ipra-final-outer-template-independent/README.md).
The 21-stage parent subsequently passed an
[independent result audit](../../reviews/trace75-bfs-compatible-forward-result-independent/README.md).

The final `run.py` pins parent result SHA-256
`f8d6388911e101a7dfae2547907bc6f9245950fa953c3a4769eff00c140fc3d8`, parent
outer terminal SHA-256
`5b286234c26c06db503ff6a485aeac2a9e57afc76205c189a30bb8e07e7316c5`, and
parent union `/tmp/trace75-compatible-forward-dbe4ma6p/lib`. The final runner
SHA-256 is `f2d43b531adb692b2bbcf27fd8c25ce79df121c85b689a9e46defcc5913130ac`;
the final outer-wrapper SHA-256 is
`cb9de001416de6373cc77e6a6c15877cbbcc864edbf395c1fd899c9d4cd8f2b7`.

Read-only preflight, tool session 33726, exited 0. Its terminal record
`observations/preflight-attempt01/terminal.json` has SHA-256
`6fb87657d5f7abc4f8f3defaf2915cb474edab21a9718f75f1e7d2454f7a4e1d`.
It reported 2,011 parent modules, 81 outside entries, five stages, and the
four inherited BFS baseline names. It did not invoke Lean.

Nineteen final-runner function controls passed; their result record has
SHA-256 `14858d9503ee16d68ad94fc7bea28c1185d628450f3242fbc96cd825de4a62d6`.
Six isolated final-wrapper stub controls passed; their terminal has SHA-256
`2f2e099a3c5d6aa00e2e14f8966a44dc93963aad10daeddbc217a3108c906e40`.
These controls do not replace a final-runner prelaunch review, a successful
Lean assembly, or an independent result audit.

After [scoped independent prelaunch review](../../reviews/trace75-bfs-final-assembly-prelaunch-independent/README.md),
the assembly was launched once. Actual outer tool session 3516 exited 0 and
was reaped; its child result is `PASS`, and the wrapper and input hashes were
stable. The final result SHA-256 is
`b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c`, and
the outer terminal SHA-256 is
`2188db777c5fe442be871c30d29943de70fe0c1d20325d49b00bb9886e56c69d`.
All five stages exited 0. The output union is
`/tmp/trace75-final-assembly-7cxl4am4/lib` with 2,016 project modules. The
fixed endpoint's selected closure contains 1,868 project and 81 outside
names. The two BFS root closures and the preserved reverse and forward graph
closures match the captured parent records under the runner's checks.
Their project/outside sizes are 46/6 for `DirectBFSBandCarry`, 855/44 for
`DirectBFSHaltPellSeed`, 965/46 for `Trace75BFSHaltGraph`, and 748/43 for
`Trace75BFSModelHalt`. All five newly built `.olean` hashes match their
exploratory predecessor hashes; byte identity alone does not establish unique
producer history.

The [independent result audit](../../reviews/trace75-bfs-final-assembly-result-independent/README.md)
checked all five stages and 14 reports, selected inputs, union inventory and
preserved closures. It did not independently replay Lean. The assembly
inherits the four named baseline source/object ancestry limits
and the other project, outside, package and dynamic limits in the
[plan](README.md); it does not establish formal JSON, TeX or PDF binding or
decide consistency.
