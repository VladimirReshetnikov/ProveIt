# Sources, revisions, and attribution

The comparison was frozen on 13 November 2026. `main` may subsequently move;
the following commits identify what was actually examined.

## James Chang: current PA196

- Repository: <https://github.com/jamesyc/BusyBeaver/tree/407cdc356f6b586635e71ac92be394255f4bfea4>
- Commit: `407cdc356f6b586635e71ac92be394255f4bfea4`
- Exact table: `data/pa196.tm`
- Literal table SHA-256: `e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`
- State bijection: `PA196/Conjugacy.lean`
- Primitive source tree: `PA196/Program.lean`
- Axiom macro word: `PA196/Source/AXProgram.lean`
- Paper: `paper/pa196.tex`
- Theorem list: `docs/result.md`
- Runtime semantics: `M6/Zip.lean`, `M6/Runtime.lean`, `M6/Native.lean`,
  `M6/Reference230.lean`
- Published compiler and physical endpoint: `PA196/CompilerCorrectness.lean`,
  `PA196/RuntimeContracts.lean`, `PA196/PhysicalEndpoint.lean`
- Logical proofs reviewed include `PA196/Logic/CommandSoundness.lean`,
  `Soundness.lean`, `Reverse.lean`, and `Neighborhood.lean`, plus their
  arithmetic-certificate counterparts.
- Internal simulation reviewed includes
  `PA196/Arithmetic/Machine/EndpointInternalCodedSourcePhysicalStep.lean`
  and `EndpointInternalCodedSourcePhysicalTrace.lean`.

The small source subset needed by the finite checks is copied verbatim under
`reference/pa196`. The three inherited Lean dependency files in
`verification/lean/M6` are upstream files. `NativeMinimal.lean` is a modified
version of upstream `Native.lean`, with its changes documented in the report
and receipt. The independent Python symbolic interpreter follows the published
runtime definitions. James Chang's MIT license accompanies these files.

## James Chang: historical PA209

- Repository: <https://github.com/jamesyc/BusyBeaver/tree/69d98241a721ead20b4f0b17df9062950b40fbfe>
- Commit: `69d98241a721ead20b4f0b17df9062950b40fbfe`
- Exact table: `data/pa209.tm`
- Literal table SHA-256: `0610d978675320f0b4b1ef34619dcd3daa5912632d7037e200dfcc70954fea51`

The exact table and its MIT license are copied under `reference/pa209`.

## Vladimir Reshetnikov / ProveIt

- Repository: <https://github.com/VladimirReshetnikov/ProveIt/tree/239b7a406e24405d464edc526e09d402abce5bc5>
- Commit: `239b7a406e24405d464edc526e09d402abce5bc5`
- Incoming archives: <https://github.com/VladimirReshetnikov/ProveIt/tree/239b7a406e24405d464edc526e09d402abce5bc5/docs/incoming>
- ConciseIPRA proposals: <https://github.com/VladimirReshetnikov/ProveIt/tree/239b7a406e24405d464edc526e09d402abce5bc5/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA>

The nine exact U208 presentations used by the graph census are copied under
`reference/proveit`, preserving their original relative paths. Their individual
SHA-256 hashes, canonical graph hashes, and full state renamings appear in
`verification/proveit_comparison.json`. The repository's MIT No Attribution
license is included. Finite local-history receipts for the two variants are
also supplied. The archive does not duplicate all eleven original research ZIPs.

## New material and scope

The new material consists of the diagonal-vacuity calibration proof, the
written PA-internal converse proof, the exact emitter modification and its
199-state compilation, the new engine-agreement lemma, comparison and
verification scripts, and bounded search programs and receipts.

The diagonal code-freshness lemma comes from the current PA196 encoding.
ConciseIPRA was considered for concise-calculus design ideas; no claim is made
that its theory can replace PA while preserving the requested consistency
sentence, or that it originated the specific diagonal clause used here.

The report and scripts explicitly distinguish written proof constructions from
kernel-checked Lean theorems. They do not establish a global state lower bound,
and no sub-196 table is supplied.
