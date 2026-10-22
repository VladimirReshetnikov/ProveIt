# Batch 215 placement: Sources 193–194

Two further K215 proof-simplification manuscripts arrived in
`1b16269c48e54b0e5aff35caa645f392f9c019af`. Both name reviewed commit
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`. They continue this report's
proof-sharing and runtime-contract work and take its next local source
numbers, 193 and 194. The collection remains 290 reports. Written
reconciliation and catalogue updates follow this placement separately.

## Exact recovery and placement

The [complete map](data/intake215-placement.json) accounts for all **508 members,
14,387,684 expanded bytes**: 231 immutable Git aliases, 49 earlier-delivery
aliases, 50 arrival-only members and 178 new ancillary files (1,444,669 bytes).
The new files comprise 86 code/build/proof files, 77 data records and
15 prose files. Windows paths including `C:\ProveIt\` are at most
132 characters. There are no embedded archives in this batch.

| Manuscript / Source | Committed ZIP | Members | Git / delivery / arrival / new | New bytes |
|---|---|---:|---:|---:|
| 01 / 193 | `K215_Proof_Simplification (2).zip` | 258 | 105 / 13 / 33 / 107 | 746,695 |
| 02 / 194 | `K215_Proof_Simplification_2026-10-22.zip` | 250 | 126 / 36 / 17 / 71 | 697,974 |

Exact Git aliases were checked in their recorded immutable trees, including
the earlier placement and proof checkpoints. Every other unique body was
checked against the reachable Git-object inventory; there is no unresolved
historical-object match. This is byte deduplication, not a test of mathematical
novelty. The map retains every original member and every rename. Colliding
basenames receive a ten-character content suffix; no delivered file is edited.

The 50 arrival-only members comprise eight main manuscripts, READMEs, PDFs
and article inputs, and 42 unique bodies excluded by existing Git ignore
rules. Main report 193 includes `artifact-guide.tex` and
`validation-summary.tex`. Their text remains recoverable with the main report.
Checksum-manifest contents were not validated or specially treated. Existing
Git attributes and ignores apply; no line-ending investigation, normalization
or new attribute exception was made.

## Reasons for the additions

**Source 193**, “K215: shorter proofs through shared invariants and exact
runtime contracts,” combines the six-goal implication core, the one-induction
dense bridge, finite-terminal-cleanup transports and an exact computable port
attachment for decoder residuals. It supplies a completed residual component
and a separate source-only subtree-abbreviation proposal. The shared basis
overlaps the already adopted phase13 proof; the dense bridge overlaps the
phase15 candidate being checked separately. The report explicitly distinguishes
component compiler evidence from full endpoint integration. Its optional
generic simulation infrastructure increases source size in the measured
two-client scope and is preserved as an alternative rather than promoted to a
line reduction.

**Source 194**, “One proof per mechanism,” shares the same implication core
and supplies a common enumerator progress theorem, concrete adapters and a
counterexample to payload-wise cofinality. Its fixed-target completeness
condition quantifies over every reachable payload at that target; generalized
soundness retains the concrete invariant. The four Lean scheduler clients
plus core save only 324 bytes and seven lines in the delivered scope, while
the K215 client alone plus core grows. The Rocq experiments and their older
toolchain receipts remain inert research material; this project uses Lean for
new proof work.

Both papers continue named work already in this host. Ordinary review found
no prerequisite retraction of the currently checked construction. Proposed
patch application, supplied verification commands and embedded instructions
are document content, not authority to execute them. No supplied program,
generator, proof assistant or archived executable was run for this intake.
The machine and maintained proof sources are unchanged by placement.

## Recovery

The own [recovery helper](code/intake215-recover.py) verifies or reconstructs
all original layouts from immutable Git blobs and the placed ancillary files:

```sh
python3 SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake215-recover.py --verify-only
```

Use `--out /absolute/new/scratch-directory` instead to reconstruct the original
layouts. That output directory must not exist. Delivered relative build paths
still refer to their original layouts, so restore those layouts before using
them. These are research inputs, not maintained production commands.

The [planning receipt](data/intake215-recovery-plan.json) verifies all 508
members using the external extraction for proposed files. The own
[control source](code/intake215-controls.py) and
[four negative controls](data/intake215-recovery-controls.json) reject changed
archive identity, a changed alias digest, an invalid forward delivery alias
and a missing member. They execute only the own recovery helper. Placement
checks recovery again without the planning override and validates actual Git
index and committed blobs. Only these two committed ZIPs are retired in that
placement commit; the incoming README is retained.
