# Generic represented sequence history: author receipt

Author: `/root/controller_certificate`, 26 October 2026. This is author
validation, not an independent review. Root authorized the generic first
checkpoint separately from its future C222 instantiation. No existing
source, shared object, frozen packet or Git state was changed.

I read the complete Foundation PRF module, the existing fixed History254
and its recurrence module, the standard Nat history comparison, and the
relevant Foundation sequence lookup/append proofs before implementation.
All new source and check files were read before execution and again in
their final form.

## Fixed syntax and explicit semantic premise

`ArithmeticSequenceHistory` imports only
`Foundation.FirstOrder.Arithmetic.HFS.PRF`. Its parameters are a **fixed**
`stepDef : Sigma1.Semisentence 3`, an arbitrary IΣ1 model V, a function
`step : V -> V -> V`, and a proof that the same fixed formula is exactly
that function's graph. No history totality or recurrence is supplied as
a premise.

`zeroDef`, `succDef stepDef`, `blueprint stepDef`, `historyDef stepDef`,
`historyDeltaDef stepDef`, `valueDef stepDef` and `valueDeltaDef stepDef`
are syntax values with no ambient-model or semantic-function parameter.
The semantic function and its graph proof are used only to instantiate
the existing `PR.Construction` for that blueprint. The underlying
primitive-recursion algorithm and its totality proof are imported, not
copied or namespace-renamed.

The initialization is the one-element sequence `[0]`; a successor appends
`step previousHistory (index+1)`. The packet proves:

- genuine Sigma1 and Delta1 graphs of history and value;
- unique evaluation of both graphs at every internal code;
- sequence validity and length exactly `code+1`;
- the final index is in range, its value is a member, and the value is
  below the encoded sequence in the HFS numeric ordering;
- zero history/value and the exact successor-history/value equations;
- every old lookup equals the value at that old index, with every lookup
  beyond the completed history equal to zero.

The induction for sequence validity, length and old-lookup preservation
uses Foundation's definable IΣ1 induction over arbitrary internal indices,
not an external recursion over standard Nat indices. The focused checks
explicitly instantiate all graph types without a model and separately
apply the totality/recurrence/lookup API with a represented semantic step.

The unique-totality theorems explicitly retain `step` and its graph proof
using `include step hstep in`; their syntax-only conclusions do not mean
that an arbitrary Sigma1 formula is total. This is the generic model-level
represented-history result. It is not yet a closed arithmetic derivation
for the actual C222 checker, a C222 seed-validity or runtime theorem, or
the requested HA equivalence. The C222 instantiation remains a separate
unimplemented checkpoint pending review.

## Frozen files and replay

Source prefix: `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

| File | Lines | Source SHA-256 | Fresh object SHA-256 |
|---|---:|---|---|
| `ArithmeticSequenceHistory.lean` | 178 | `764b832d28249b17d640a7a3a2b3721deb90a0ee82360e48331be6dabd0d9a3d` | `6fbbbe4bd63cdd7311ffc0c21f0209a34a831ceb460aa81171c2ce5207291db9` |
| `ArithmeticSequenceHistoryChecks.lean` | 47 | `d7b4b09a3403dfcdd151a566ceb6332ccea8df36cd330922aa742e2302cc9aea` | `715c0eaea7af5ee491ca0eccc57cbf6cd345440f3ac38817ab8284d322135a75` |

The final main/check pair passed under `-M6000 -j1 -DElab.async=false`.
The main log is empty. All 15 intended reports contain only `propext`,
`Classical.choice` and `Quot.sound`; no new axiom, sorry or native decision
oracle was added. Final aggregate time was 8.03 seconds and maximum RSS
1,805,144 KiB.

The private overlay `/tmp/sequence-history-controller-r1ujbe6v/lib` reuses
95 exact-source Foundation prerequisites and records 37 external
precompiled import boundaries. The accepted growG/arithmetic-base
provenance is retained; this task freshly compiled only the two new
wrapper leaves. No Foundation, package or broad closure rebuild occurred.
All selected source/object/companion pins were checked before and after
the commands, with a 512MiB reserve enforced before each invocation.

Pre-execution inventory SHA-256:
`178466663847772ae4480a7fff2d9c5feda836c4ea591a04d38c7a345e47919a`.
Compiler SHA-256:
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Package manifest SHA-256:
`95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`.

The central imported PRF source is
`5925b829137d35293fa00955e81a584857e49a3db94baff1810b44bd05c7beeb`,
with object `068ab5c4ae259a4eeff277a4cf4bcf94d690c8aaac58f242879057b32063d932`.
Its sequence source is
`b2f1f9fbd0c746aa1f531ba4a468bf07f24eab388b7fd4c924abe240429517a8`,
with object `45aa16d07ef64b54e459449404033730cdb482d832dc050728f2267630caf923`.

Complete inventories, snapshots, commands, logs, timings, object pins and
reports are in `arithmetic-sequence-history-replay.json`, SHA-256
`c21618568efb69a1516ad30ae2d7ed833345785b8db803a71e8badac7016cd66`.

## Preserved development failures

The first draft used bare simplification for the two totality corollaries;
Lean correctly failed because the syntax-only conclusions omitted the
section's semantic step and graph premise. A second draft explicitly
used the graph witnesses, revealing the same omitted-parameter issue as
unknown `step` identifiers. The final explicit `include step hstep in`
retains the intended premise and proves existence/uniqueness directly
from the already-proved graph. Both rejected sources and logs remain
separate. No graph, construction, recurrence or lookup proof changed.
