# K216 alternatives: permuted commands

**Accepted after all ten selected fresh checks and the independent saved-output audit passed.** These are the Source159 command-permutation alternatives, each with 216 working states including blank initialization. The [partial-selector K216](../../README.md) remains the primary candidate. The next target is 215 or fewer working states.

The ordinary proof connects each exact table to the inherited numerical calculus. The separate source, runtime and startup obligations are now discharged, giving:

```text
ZFC proves: not Halt(machine, blank) ↔ Con(ZFC).
```

This is an ordinary proof formalizable in ZFC. It does not assert ZFC consistency, unconditional nonhalting, minimality, or a newly checked exact-table Lean/Rocq/internal-PA endpoint. See [proof.md](proof.md) for the source compiler, cofinal enumeration and physical composition.

## Exact alternatives

Both machines use a two-way infinite binary tape, blank0, initial head0 and start state0, with only L/R moves. There are 216 working states and 432 transitions; the separate halt has no outgoing rows and is excluded from that count. A row is `state read write direction next`. Canonical labels are 0–215 with halt 216; native halt is 254. All working states are directed-graph reachable, which does not assert that every state occurs on the blank run.

| Artifact | Primary permutation210 | Secondary permutation120 |
|---|---|---|
| Canonical table | [k216.tm](k216.tm) | [k216-120.tm](secondary/k216-120.tm) |
| Native table | [k216.native.tm](k216.native.tm) | [k216-120.native.tm](secondary/k216-120.native.tm) |
| State bijection | [canonicalization.json](canonicalization.json) | [canonicalization.json](secondary/canonicalization.json) |
| Complete source | [sites216.json](sites216.json) | [sites120.json](secondary/sites120.json) |
| Compact source | [sites216.compact.json](sites216.compact.json) | [sites120.compact.json](secondary/sites120.compact.json) |
| Small command tags | NIP0, DROP1, MP2 | DROP0, NIP1, MP2 |
| Deleted parent state | 163 | 134 |

AX keeps tag `c+3` and input wire order `[c+3,y,x]`. Each source has 202 distinct subtrees, 4,751 primitive occurrences, 6,176 guarded cases, depth 44 and maximum zero run 6. Each physical decoder uses 166 states, with 50 other states.

| Exact bytes | SHA-256 |
|---|---|
| Primary canonical | `b0cf986df02fc0383c788f3d06ac46ac179ed81b3f1546115668c13bf72eeaea` |
| Primary native | `eff4f5a3e2c81a674d1a799f634ee4606708b79899e65e8c3cb688dc87c954a3` |
| Primary source | `8b5dc46f10d927b2db5e4bcb522d482779ec61c72c82717d7bf12fca3550a3bc` |
| Secondary canonical | `0e384c502134e67897a998fc679bcb7f7d2172000e54279b304a9c40bb8ab753` |
| Secondary native | `be663ef8daf05d42ad6f0c9972f4a3e7bd18e55f84d8c83f5c7b0867221fbb72` |
| Secondary source | `ee1f7c7cb216a80315449371b040ee094728a655439954225ed4be4635296680` |

## What changed

The source removes the common counter reader and moves each needed read into the relevant arithmetic command. Two closed reassociations give a 202-subtree source with zero-run bound 6. Permuting the three closed small command bodies changes the selector interpretation and makes blank initialization reach a clean theorem seed. The all-natural compiler is written in command names and then encoded with the new tags; the proof includes arbitrary raw numerical inputs and the alias `I(0,0)=0`.

The physical allocation reuses the existing path `81/0=0L111`. Its old and new fragments have identical three-step whole-tape endpoints for either neighboring bit, freeing the old 92/1 role. Each deterministic recipe changes 38 retained rows and deletes one parent state without adding a state. The complete symbolic primitive proof is needed for all the other decoder changes.

These tables are distinct from the primary partial-selector216 construction. Its state201 helper now has other decoder duties, so copying that fold is not a verified215-state combination. The202-subtree count alone does not establish another physical saving.

## Verification and reproduction

Root executed ten selected fresh leaves: deterministic source rebuild; two exact command-permutation checks; independent primary source correspondence; both table rebuilds; primary machine/local-helper audit; independent primary and secondary blank replay; two complete symbolic runtimes. The [actual record](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake197-fresh/actual.json) retains every pass; the [independent saved-output audit](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake197-fresh/actual-review.json) checks the individual obligations and exact input/output identities.

The fresh results reproduce the delivered case lists, complete startup traces and rebuilt artifacts exactly. Runtime receipts differ only in execution timing.

| Obligation | Permutation210 | Permutation120 |
|---|---:|---:|
| Complete blank startup | 95,674 transitions | 96,244 transitions |
| Symbolic primitive cases | 6,176 | 6,176 |
| Symbolic rules | 1,605,450 | 1,605,505 |
| Minimum affine duration constant | 6 | 9 |
| Transition rows covered | 432 | 432 |

The quantified runtime phases took 162.903 and 161.280 seconds respectively. The two processes ran in parallel with separate outputs and 360-second caps. No submitted candidate source was modified. The runner did not record a historical before/after hash map; the independent review binds the selected current disposable inputs to the pristine package and exact inherited pins.

Both startup endpoints are native dispatcher84/canonical83, head−8, header 57, gap 1, registers `[4,0,0,0,0,0,0,0,0]`, forty unit spares and exactly 95 one-cells, with zero exterior. Independent replays compare complete traces and reconstruct this entire frame.

The runtime proof has arbitrary independent natural register values, arbitrary natural gap and any nonempty finite list of natural spare values. Literal transitions and unary/list induction establish complete tape endpoints with positive progress. The 4,000-rule construction cap is not a bound on represented values or concrete running time. No new proof-assistant build or inherited logical-suite replay is part of this intake. Stored C++ receipts remain delivered comparisons; no fresh C++ compilation is claimed.

See [intake197](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-197.md) and its [reproduction guide](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-197-reproduction.md) for direct commands, original recovery, full source/proof references and fresh records. The submission's source README lists several absent standalone documents and output paths; these are historical references, not additional recovered files. The explicit reproduction guide uses the actual shipped code paths.

## Attribution

Source159 arrived in commit `d59b441882`. Its reader schedule, helper reuse, permutations, exact tables and proofs are submitted ChatGPT-assisted work for Vladimir Reshetnikov's ProveIt project. The dominated calculus and certificate, source language, arithmetic macros, runtime engine and earlier machine architecture retain their original authorship. [NOTICE.md](NOTICE.md), [original attribution](provenance/ATTRIBUTION.md) and [licenses](licenses/) preserve that boundary.

`drop_contract` reviewed the full ordinary mathematical argument and selected code closure and wrote this exposition. `review_upstream_reflection` independently compared literal sources, transitions and predecessor bindings and audited the saved fresh results. Root owns fresh execution and publication. These review roles do not transfer authorship of the submitted construction.
