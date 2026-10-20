# K-theory 221-state candidate

This binary, single-tape machine has **221 working states**, including initialization, plus
a separate halt state. It starts in state 0 at head 0 on an all-zero two-way infinite tape.
Every transition moves left or right. The complete 442-row table is [zfc_k221.tm](zfc_k221.tm).
**It is the smallest known candidate** whose blank-tape non-halting is equivalent to Con(ZFC).

The construction is **Source 132** (`K221_Construction_2026-10-20.zip`, arrival `c011e44bc2`),
placed in `c92e98e674`. It starts from Source 131, the seed-K 222. That machine is the same
composition as the intake's [variant-bc](../candidate-k222/variant-bc/README.md): Source 128's
merged equality row G with Source 129's seed presentation of K.

An ordinary mathematical proof, formalizable in ZFC, gives

  ZFC ⊢ (this machine does not halt from the blank tape ↔ Con(ZFC)),

because the 221 runs the seed-K 222's register program unchanged (below). **No Rocq or Lean
theorem exists for this table**, and no proof internal to PA. No absolute consistency,
unconditional non-halting, minimality, or two-sided independence from bare consistency is
claimed.

## What saves the state

**Three closed rotations.** The source is the 222's, re-associated at three places
(`portable/inputs/explicit_rotations.json` in the package):

- one left rotation at path `11101001001110111110`;
- two left rotations at path `111010010011101`.

A rotation changes neither the primitive word nor any guarded branch target. What it changes
is which tape-address tag each decoder state sees on arrival.

**One fold.** After the rotations, native decoder states K172 and K192 can share a state:

- on read 1 they already act identically;
- on read 0 they are separated by the bit just left of the head, which is 0 at K172 and 1 at
  K192 on every arrival.

The kept state's read-0 row becomes `(0, L, K112)`. The existing helper K112 reads that bit
and continues each context to its old successor, in five steps for K172 and three for K192.
No state is added. The tags are not sampled: they come from an inductive tape invariant of
radius 8, computed from an unconstrained initial state.

**Accounting.** The source keeps 4,744 primitive occurrences and 208 distinct subtrees
(23 primitive types, 185 interior). Thirteen tag-shared roles instead of the 222's twelve give
49 engine states + 185 nodes − 13 = **221**. Depth is 38 (36 before the rotations); the
maximum zero run stays 6.

## Why the calibration transfers

The calibration is the seed-K 222's: Source 129's seed presentation of K, composed with
Source 128's G equivalence. It needs only that the 221 runs the **same register program**,
and the intake checks this directly against variant-bc's source
([record](evidence/cfg_identity.txt)):

- the primitive word (leaf sequence) is identical;
- the guarded control-flow graph is identical under both independent resolvers (arithmetic and
  interval), on all 6,167 checks, including entry and halt ordinals.

The logical calculus is therefore unchanged. The package's new contribution is the source
layout, the extra sharing, the literal table and its simulation certificates; it adds no new
axiom or logical row.

## Verification

These are the intake's own replays on the relabelled table ([zfc_k221_old.tm](zfc_k221_old.tm)).

| Check | Result |
| --- | --- |
| Unbounded runtime of **this table** on its own source, with Source 103's checker ([receipt](evidence/runtime221.json), [cases](evidence/runtime221_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: **6,167** guarded cases, **1,514,663** symbolic rules, all 442 rows, minimum instruction duration 13 |
| Exact blank startup, sparse and dense ([code/boot.py](code/boot.py), [record](evidence/boot.txt)) | the complete dispatch frame after **409,835** steps |
| Finite screen on every leaf and both decrement guards ([record](evidence/screen.txt)) | 0 of 6,167 failures |
| Source against variant-bc ([record](evidence/cfg_identity.txt)) | same leaf sequence; guarded CFG equal under both resolvers |
| Canonical, inherited and K-label tables | one machine (BFS-canonical forms equal, all 221 states reached) |
| Fold detector calibration ([code/sim_fold.py](code/sim_fold.py), [code/rot_fold_search.py](code/rot_fold_search.py)) | replaying the three rotations on Source 131's table, the detector finds exactly this fold (and its mirror) |

The package also ships its own certificates: two separately written all-tape fold checkers,
the decoder binding at every compound occurrence, 32,107 invariant closure checks and a fresh
runtime replay. The intake did not rely on them.

## Exact files

| File | Meaning |
| --- | --- |
| [zfc_k221.tm](zfc_k221.tm) | Canonical table: states 0–220, start 0, dispatcher 22, halt 221. |
| [zfc_k221_old.tm](zfc_k221_old.tm) | fold241 inherited labels (start 95), the table the intake's checkers ran on. |
| [sites_logical.json](sites_logical.json) | Exact 4,744-leaf rotated source. |
| [ingredients/](ingredients/) | The package's K-labelled table, and the 222-state K-labelled table after the rotations and before the fold. |

Canonical SHA-256 `6457dce8c91c5975fb405607567158ca92ad97331f2724503edc0d4ff74cab3c`;
inherited `907913d97ad1b7dc7969ac776d63dbc904a00f432052290eccfe2dd5d825c794`; source
`691684ec948c972bf67727d6d4cd1181a90a9203644ee3db3eae363280e3fac9`.

## Below 221

See the [batch 183 reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-183.md):
the four 222 packages of the same arrival, and the rotation-chain fold search the intake ran
from this table.

See [ATTRIBUTION.md](ATTRIBUTION.md).
