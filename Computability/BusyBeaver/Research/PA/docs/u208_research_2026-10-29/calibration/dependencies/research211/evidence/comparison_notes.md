# Comparison of the eight U212 packets at the pinned current snapshot

## Exact construction consensus

The seven complete, readable ZIPs contain byte-identical native machines:

`386ce16259d4c97e4af31b3ba494feaff11a0a1a066e0235dddc154b4cea38c4`.

They also use the same 3,909-leaf, 197-distinct-subtree source, with SHA-256
`7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00`.

The current archive with suffix `(5)` has a truncated/corrupt ZIP structure.
The root agent recovered CRC-verified early members. Its intact builder,
construction receipt, README and intact direct-transfer U213 parent specify
the same two-row construction and exact same expected native/dense/source
hashes. Its missing final machine should be described as reconstructed from
recovered inputs, not as directly read from an intact archive member.

Every construction selects the direct-transfer U213 parent with native hash
`bb4f5ac12b29d07d1080109af9bb564e9e11a4783efc48cd73b8f826789d01f7`,
then makes exactly these edits:

- `180/1: 1 R 172 -> 1 R 211`;
- `172/0: 0 L 112 -> 0 L 67`;
- delete native state 112.

There is no additional state saving available by adding these eight final
patches: they are the same patch, including the same semantic helper 211.
The physical result is 212 working states, 424 binary transitions and a
separate halt. The original U213 comparisons reproduced inside the packets
are comparisons of genuinely different predecessors; this must not be
mistaken for eight different U212 machines.

## What differs usefully among the packets

| Current packet | Distinct contribution in its presentation or validation | Assessment |
|---|---|---|
| `U212_ConPA_Stacked_2026-10-28.zip` | Direct local whole-tape reduction, explicit retained endpoint audit, independent local checks, and several exploratory bypass/scanner searches. | Sound baseline organization; includes an unmodified complete U213 ancestry archive. |
| suffix `(1)` | Clear two-stage proof and direct checkpoint time bound `T212 <= T213 <= 7/3 T212`; two local checkers; explicit six-zero-detector counterexample; concrete tagged-rotation stacking obstruction. | Particularly useful exposition and negative controls for further research. |
| suffix `(2)` | Independent path and local-frame implementations; explicit 6,768-frame verification; calibration audit; portable full replay. | Strong redundant local checking and concise proof separation. |
| suffix `(3)` | Separate intermediate table, independent two-stage audit, rejected circular alias, and exact input comparison; parent source and runtime modules preserved. | Particularly clear treatment of why helper re-use must be checked against the final table. |
| suffix `(4)` | Independent block and path checks plus the most explicit bounded-search ledger: direct aliases, deeper synchronization, entry bypasses, entry-specific targets and direction reversal. | Best source for avoiding duplication of already unsuccessful narrow searches; no minimum-state theorem follows. |
| suffix `(5)` | Recovered README, builder, receipts and comparison notes give the same local proof, 5,084 symbolic contracts, finite startup and detailed unsuccessful role-based stacking analysis. | Useful recovered corroboration; damaged archive cannot be advertised as fully replayable as delivered. |
| `U212_ConU_2026-10-29.zip` | Two-stage simulation, explicit source-prefix binding, two independent local frame counts (6,816 then 6,768), full `56+g` runtime frame and startup block treatment. | Good proof-layer separation, especially the interior-start and arbitrary-tail calibration. |
| `u212_combined_2026-10-29.zip` | Compact flattened baseline dependencies, independently checkable source/calibration inventory, hash-preserved inherited sources, comparison inputs, runtime56 engine, startup/seed and mutation checks. | Best practical starting point for a new compact reproducible artifact because the needed baseline files are already directly accessible, rather than hidden through several nested ZIPs. This is an organizational choice, not evidence of a stronger machine theorem. |

All complete packets have the same essential proof status: an ordinary
mathematical literal-machine reduction, finite independently replayable
local identities, and unary/list-inductive runtime evidence. None contains
a newly compiled full Lean/Rocq/MM0 consistency endpoint for U212. Their
Con(U)/Con(PA) endpoint is inherited through the stated numerical-calculus,
compiler, startup and unary-theory arguments. The separate fixed K215/ZFC
theorem is not a certificate for this changed machine.

## Relevant unsuccessful searches already present

The suffix-(4) packet's `research/bounded_search_receipt.json` documents:

- direct state substitutions in all eight U213 tables and the U212 table;
- tape-bit invariants at radii four or six, synchronization depths 10 or 20;
- radius-three pattern invariants for one U213 allocation;
- an invariant-strengthening bypass followed by a state substitution;
- per-entry helper selection with possible direction reversal, final edited
  table rechecking, and a cap of 500 combinations per removed state.

These fail to find a further reduction. They do not accelerate arbitrary
unary loops and may miss source-specific invariants. The suffix-(1) and
ConU packets additionally record that the known tagged-selector rotations
repurpose helper 211, which the U212 bypass now enters from 180/1. This is
a concrete obstruction to those literal recipes, not a general obstruction
to a different allocation or helper.

## Incremental compiler availability

Recursively inspected the retained U213 -> U214 -> U218 -> U222/U221 ZIP
chain. Its `build_table.py` variants replay fixed patches and recipes;
the general context-sensitive allocator used in discovery is not supplied
there. A fresh source candidate therefore needs a reconstructed allocator
or a literal decoder transformation with separately checked guards, followed
by universal primitive replay and startup calibration. Prefix correctness
alone is insufficient, as the combined packet's inherited allocation notes
already show by a counterexample involving a runtime reentry row.
