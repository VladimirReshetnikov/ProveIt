# Independent result review: trace75 BFS model halt

**PASS.** The captured author result for `Trace75BFSModelHalt.graph_halts`
has child, Lean and serialized-header exits 0, the expected axiom report,
and matching source, output, logs, pins and three direct imports. The author
reports actual outer tool exit 0; the wrapper records child exit 0 and stable
hashes. This review did not replay Lean.

Under the exact symbolic direct-BFS port equalities and a positive trace75
zero in an IΣ₁ model V, the theorem concludes that there is t:V with
`first (ArithmeticMachineRun215.run t)=0`. It feeds the predecessor's
`CompactLocalWord.Word` over the backward-mapped row to marked-word
identification and model soundness. This is one model-level direction, not a
claim of standard halting, halt iff, iPRA derivability or external file binding.

The accepted result SHA-256 is
`f07f6309693b7259e15bd149a14c2da5e96e50c62b5fc82c43ca60d4fa416a4a`,
and its outer receipt SHA-256 is
`131436b3c3edc596212719a52fb88c0ad62dfa5016fc98ce089610323fc376d3`.
The regular output `/tmp/trace75-bfs-modelhalt-ipf6iwvw/Trace75BFSModelHalt.olean`
has SHA-256 `f3334e5e331cf93540fc45b92d221c4879bc2c0847068b38d96eae83561f56ae`.

The actual recorded Lean search order selects output, 20 guarded client roots,
the fresh union and package. The check rehashes those roots, 1,977 project and
80 outside bundles, targets and first resolutions, and captured BFS subtrees
`OldWordIdentification` (526 project/42 outside) and
`ArithmeticWangSoundness` (135/8). Historical source/object, unrebuilt,
package/dynamic and external-file limits remain; these checks do not establish
full ancestry.

`check.py` SHA-256 `a459cce53515f5c799c6f86b542d3b9995af684afae714f438f4d39bb786cddc`;
`result.txt` SHA-256 `f10159b98c1c98a942f706a9cf899a68bd078fdc4c245ae40c093ebc7bb5e547`.
