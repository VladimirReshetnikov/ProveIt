# Rotated 236-state candidate

This binary, single-tape machine has **236 working states**, including
initialization, plus a separate halt state. It starts in state 0 at head 0
on an all-zero two-way infinite tape. Every transition moves left or right.
The complete 472-row table is [zfc236.tm](zfc236.tm).
**It is the smallest known candidate** whose blank-tape non-halting is equivalent
to Con(ZFC).

It removes one more state from the [237-state candidate](../candidate-composed237/README.md).
That machine in turn removed three from the [240-state candidate](../candidate-rotation240/README.md).
The construction is Source 112 of the ZFC closure-kernels host, delivered on
19 October 2026 (arrival `0b5fec6980`). An ordinary mathematical proof, formalizable
in ZFC, establishes

  ZFC ⊢ (the machine does not halt from the blank tape ↔ Con(ZFC)).

It composes an unbounded executable runtime certificate, an exact blank startup, a
certified source equivalence, an all-tape local fold and the inherited source
calibration. Every part was re-checked independently by the intake.

**No Lean or Rocq theorem exists for this table**, and no proof internal to PA.
The checked Lean endpoints stop at the 240-state machine. No absolute consistency,
unconditional non-halting, minimality, or two-sided independence from bare
consistency is claimed.

## How the state is saved

The step from 237 has two parts. Net of the 240 table, states 169, 218, 223 and
235 are deleted, 49 retained rows change and 423 are unchanged
([construction.json](construction.json) lists every stage).

### 1. A node-neutral source rotation (237 → 237)

In the register program, replace `(A,(B,C))` by `((A,B),C)` for three closed chunks
of 245, 160 and 132 instruction leaves. The middle node's decoder state 185 is
reused for the new inner node `(A,B)`, so the DAG keeps its 224 distinct subtrees,
and the decoder changes in exactly four rows:

| Row | Before | After |
| --- | --- | --- |
| `177/0` | `0 R 165` | `0 R 185` |
| `177/1` | `1 R 185` | `1 R 212` |
| `185/0` | `0 R 192` | `0 R 165` |
| `185/1` | `1 R 212` | `1 R 192` |

The rotation moves 537 instruction paths. The maximum depth rises from 48 to 49, and
the longest zero run stays 6. The source's complete control graph is unchanged: the
same 6,455 ordered instructions, with the same targets on all 8,386 guarded edges.

### 2. A fold made possible by the rotation (237 → 236)

Delete state 223, redirect its only incoming row `237/0` to 182, and give 182 the rows
`0 L 198` and `1 L 210`. Old 182 is entered only by `76/1 = 1 R 182`, so it always has a
1 to its left. Old 223 is entered only by `237/0 = 0 R 223`, so it always has a 0. The
merged state looks back at that bit:

| Old row | Left | New path | Steps |
| --- | --- | --- | ---: |
| `182/0` | 1 | 182 → 198 → 136 → 187 | 3 |
| `182/1` | 1 | 182 → 210 → **177 → 212** | 3 |
| `223/0` | 0 | 182 → 198 → 206 → 23 | 3 |
| `223/1` | 0 | 182 → 210 → 114 → 70 | 3 |

Each path reproduces the old step's whole tape and head position. The invariant holds
on **every** initial tape, so the fold needs no runtime premise. The path for `182/1`
uses the rotated row `177/1 → 212`. Without the rotation that row does not exist, and
the fold is not available on the 237 table.

## Verification

| Check | Result |
| --- | --- |
| Direct unbounded runtime of **this table** on its source: Source 112, and replayed by the intake with Source 103's checker, its source pin removed ([receipt](evidence/runtime236_intake.json), [cases](evidence/runtime236_intake_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: **8,386** guarded cases, **2,267,815** symbolic rules, all 472 rows, minimum instruction duration 13 |
| Exact blank startup, sparse and dense ([code/boot.py](code/boot.py), [record](evidence/boot236_intake.txt)) | the complete frame after **409,835** steps, as for the 237 |
| Rotation, source equivalence, fold invariant and the four blocks ([code/check236.py](code/check236.py), [record](evidence/check236_intake.txt)) | all pass, re-derived from the literal files |

The runtime checker is an induction engine over all natural register values, an
arbitrary gap and an arbitrary finite spare list; its 4,000-rule cap bounds proof
construction, not machine time. The only adaptation to it is the removed hash pin of
Source 103's source; this machine runs Source 112's rotated source, certified separately
above. Its case data and rule count match Source 112's delivered proof exactly.

The startup frame is head −5, marker −6, header 176, 351 one-cells, logical
registers `(3,0,0,0,3,0,0,0,0)` and 167 spare blocks of value 1, with every other
cell 0. The new rows of 182 are not visited during startup.

**Looking for 235.** The intake repeated Source 112's method one level further. On
this table it compiled every node-neutral rotation that repurposes one decoder state
(21 of them, then their rotations in turn), and ran Source 112's fast fold search and
Source 106's helper search. No sound fold appeared. One rotation exposed a fold
merging 157 into 116, but that rotation flips the entry bit of the tag-shared state
153. That breaks 159 instruction cases, and 157 is exactly the state that reads the
tag. The record is in the
[batch 175 reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-175.md).
These are bounded searches, not lower bounds.

## Exact files and attribution

| File | Meaning |
| --- | --- |
| [zfc236.tm](zfc236.tm) | Canonical table: states 0–235, start 0, dispatcher 84, halt 236. |
| [zfc236_old.tm](zfc236_old.tm) | Inherited labels: start 95, dispatcher 96, halt 254. |
| [sites_logical.json](sites_logical.json) | Exact 6,455-leaf rotated source (224 distinct subtrees, depth 49). |
| [renumbering.json](renumbering.json) | Canonical state bijection. |
| [construction.json](construction.json) | Every stage from the 240 table: hashes, deleted states and row edits. |
| [provenance.json](provenance.json) | Delivery, placement and the intake's fresh checks. |
| [ingredients/](ingredients/) | The composed and rotated 237 tables and the composed 237's source. |
| [code/](code/) | `check236.py`, `make_construction.py`, `boot.py`. |
| [evidence/](evidence/) | The intake's runtime receipt with per-case records, startup and check records. |

Canonical SHA-256:
`d4302309401891d68b93c393e4ad6e24d2abf993dede4a61baa2d3e0c1c53c8e`.
Inherited SHA-256:
`ff059535876bc9e1e1e63174ebfd1c10a91c1a818ba0c3f8c4ef2ac51a3cfcc3`.
Source SHA-256:
`1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f`.
Each non-comment row is `state read write direction next_state`.

The original calculus, program and 254-state construction are credited to Mira-Cult,
upstream verification to Jeff Ketchersid, and the compiler framework to Andrew James
Wade. ProveIt and its earlier incoming reports keep credit for the reductions to 240,
and the reductions to 237 are credited as on the
[237-state page](../candidate-composed237/README.md). The rotation-enabled fold to
236 belongs to Source 112. See [ATTRIBUTION.md](ATTRIBUTION.md). The inherited
licenses and notices are kept under `licenses/`, without relicensing.
