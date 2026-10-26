# Actual Nat C222 checker: author receipt

Author: `/root/controller_certificate`, 26 October 2026. This is author
validation, not an independent review. Root authorized only a new standard
Nat checker and focused checks. Existing sources, shared objects and Git
state were left unchanged.

I read the complete `Code254Proof` parser, all twelve actual `KCode222.C222`
constructors and the shared formula constructors before implementation. I
read the complete two new files before execution and again after the single
proof-script correction recorded below.

## Exact result and semantic boundary

`Code222Proof` reuses the **syntax-only** `Code254Proof.RawProof` datatype,
its `quote`, `height`, `height_le_quote`, `decodeFuel` and `decode_quote`.
The raw constructor named `.r7` retains its tag9 numeric encoding, but the
new recursive `conclusion222` maps it to the actual `KCode222.growG`.
The bundle node maps to actual `KCode222.bundle222`, without the C254
equality-vacuity helper.

`valid222` recursively validates both MP children and compares their
**new** conclusions. Generalization validates its child. The bundle gate
remains exactly `c != a` and `c != b`. Every other leaf is one of the
unchanged actual C222 rule constructors. Neither the old `RawProof.valid`
nor the old semantic soundness/completeness theorem is invoked.

`sound` is a new structural proof into actual `KCode222.C222`.
`rawProof_exists` inducts on an actual C222 derivation and obtains a finite
raw tree inside a proposition; it does not eliminate a Prop derivation into
a selected computational tree. The unchanged parser roundtrip then proves

```text
KCode222.C222 n <-> exists code : Nat, check222 code n = true.
```

The checker parses with the explicit fuel `code + 1`, checks the new
recursive validity, and compares the actual conclusion with the requested
natural number. It is defined on every Nat, including malformed codes.
The focused file checks tag9's unchanged quote, its new literal growG
conclusion, the helper-free bundle conclusion, the complete MP guard,
zero rejection, truth acceptance, general growG acceptance, the legal
`a=b=1,c=0` bundle, and both forbidden bundle collisions.

This is an external numerical checker theorem. It does not yet represent
the C222 row/history in IΣ1 or PA, translate C222 seed validity, connect
the actual enumerator or 215-machine runtime, or prove the HA equation
equivalence. The earlier growG and seed circuit packets remain frozen.

## Frozen sources and successful objects

Source prefix: `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

| Source | Lines | Source SHA-256 | Fresh object SHA-256 |
|---|---:|---|---|
| `Code222Proof.lean` | 132 | `7e91fc3c3fca914db3b9063003e273dfa49f773c20366f61b23afe79ac48d1f5` | `c7d6713935acd3a914bb1ce659340c6fe11034f383850177fa414a6c4cdc1b0d` |
| `Code222ProofChecks.lean` | 51 | `d5b3af67bdb9a338c5252e6863d8b5580d99a5ed66b9c478fd0c157ad3e35206` | `79f8d98dbdd18399b1848232f16601e8117e9069c9200a634a2b778f14a7989c` |

The final main/check commands both exited zero under
`-M6000 -j1 -DElab.async=false`. The main log is empty. All nine intended
axiom reports contain only standard Lean axioms: five report `propext`
alone; four additionally report `Classical.choice` and `Quot.sound` through
the imported parser roundtrip. No new axiom, sorry or native decision
oracle was introduced. The final pair took 1.13 seconds, with maximum
RSS 475,568 KiB.

The private overlay is `/tmp/code222-controller-mhs20gs0/lib`. It reuses
13 selected project prerequisites by their exact source/object pins and
one explicit `Init` toolchain boundary. There are no Foundation imports
in this selected closure. The prerequisite provenance is the accepted
growG receipt and its source-authenticated arithmetic215/current-closure
providers; this task freshly compiles only the two new leaves.

The pre-execution inventory SHA-256 is
`16f8be346d906628922ec95c244d1c48ebab2c33f6a2a308f5fcf5729e481270`.
All selected prerequisite source/object, compiler and manifest hashes were
reauthenticated before and after compilation. The compiler SHA-256 is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`;
the package manifest SHA-256 is
`95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`.
The driver checks the 512MiB disk reserve before every invocation.

Complete pins, snapshots, commands, logs, timings, reports and development
attempts are in `code222-proof-replay.json`, SHA-256
`a854e8bac4a703a5e801483943af53904e79548216b9a0863f31d5c5805cb5e9`.

## Preserved development failure

The first main compilation failed only in the final `accept_bundle`
corollary: a restricted simplifier list did not discharge the two
`decide` expressions using the freshness hypotheses. The proof was
replaced by explicit `Bool.and_eq_true` / `decide_eq_true_eq` followed by
the two given hypotheses. No checker definition, theorem statement,
semantic induction or parser use changed. The failed log and exact source
snapshot are retained separately. The subsequent main and first focused
checks both passed; no prerequisite or shared object was overwritten.
