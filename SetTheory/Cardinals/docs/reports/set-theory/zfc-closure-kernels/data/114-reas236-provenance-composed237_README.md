# Composed 237-state candidate

This binary, single-tape machine has **237 working states**, including
initialization, plus a separate halt state. It starts in state 0 at head 0
on an all-zero two-way infinite tape. Every transition moves left or right.
The complete 474-row table is [zfc_composed237.tm](zfc_composed237.tm).
**It is the smallest known candidate** whose blank-tape non-halting is equivalent
to Con(ZFC).

It removes three more states from the [240-state candidate](../candidate-rotation240/README.md),
by three independent savings delivered on 19 October 2026. Each is
described below with its exceptional paths. An ordinary mathematical proof,
formalizable in ZFC, establishes

  ZFC ⊢ (the machine does not halt from the blank tape ↔ Con(ZFC)).

It composes an unbounded executable runtime certificate, an exact blank startup, a
certified source equivalence and the inherited source calibration. The runtime
certificate has been replayed independently.

**No Lean or Rocq theorem exists for this table**, and no proof internal to PA.
The checked Lean endpoints stop at the 240-state machine: the
[external endpoint](../rotation240_binary.md) and, in progress, its internal PA
comparison. No absolute consistency, unconditional non-halting, minimality, or
two-sided independence from bare consistency is claimed.

## How the states are saved

The three savings touch disjoint rows. Net of the 240 table, states 169, 218 and
235 are deleted, 45 retained rows change and 429 are unchanged
([construction.json](construction.json) lists every edit at every stage). Each
saving is a positive block simulation: every old step either agrees with one new
step through a state map, or is reproduced by a short block that ends with exactly
the old tape, head position and mapped state. The tables below give these blocks.
"Left" is the tape context the old state is known to have; [code/check_blocks.py](code/check_blocks.py)
re-derives every path from the literal tables, on every admitted five-cell window.

### 1. Source boundary: 240 → 239 (state 218)

The register program is a binary tree of instruction leaves, run by a decoder in
which every distinct interior subtree costs about one control state. A certified
reparenthesization of the program reduces its distinct subtrees from 225 to 224. It
uses 13 stages with 25 rotations, and keeps every one of the 6,455 instruction
occurrences, register operands and control-flow successors. The longest path drops
from 51 to 48, and the longest zero run stays 6. The two last rotations cross a
trailing break, using the lemma `((P;Q);break k) = (P;(Q;break k))` for closed `P` and
`Q`.

Re-encoding the decoder for this source gives the 240-state intermediate
`boundary240`, in which 37 rows of 20 decoder states change. That frees one sharing.
State 218 used the bit behind the head to tell its two roles apart. Now it is split
by that bit: its role with left bit 0 goes to its former helper 223, and its role
with left bit 1 merges with 179. Three control roles thus occupy two states.

| Old row | Left | New path | Old steps → new |
| --- | --- | --- | --- |
| `179/1` | 0 | 179 → 215 → 183 → 213 → 237 → 105 | 1 → 5 |
| `218/0` | 0 | 223 → 23 | 3 → 1 |
| `218/0` | 1 | 179 → 105 | 3 → 1 |
| `218/1` | 1 | 179 → 215 → 233 → 70 | 1 → 3 |

The other two `218`/`179` cases take one step on both sides. An inductive incoming-tag
relation from state 95 makes this valid for **every** binary initial tape, with no
runtime premise.

### 2. Delayed erasure: 239 → 238 (state 169)

Delete state 169 and change three rows: `147/0 → 0 R 80`, `80/0 → 0 L 106` and
`91/1 → 1 L 167`. The key change is at `91/1`, which previously erased its 1. The 1
is now kept for a moment, so the shared states 167 and 151 can tell the original
caller from the merged role of 169.

| Old row | Left | New path | Steps |
| --- | --- | --- | ---: |
| `80/0` | 1 | 80 → 106 → 92 → 107 → 125 → 25 | 5 |
| `169/0` | 0 | 80 → 106 → 93 → 57 | 3 |
| `169/1` | 0, right 1 | 80 → 91 → 167 → 151 → 173 → 56 | 5 |
| `91/1` | 011 | 91 → 167 → 151 → 24 → 36 → 54 → 71 → 82 → 94 → 50 | 9 |

The left bits come from a syntactic predecessor invariant: states 67, 80, 91 and
169, closed on 121,024 windows. The `169/1` block also needs one **runtime guard**:
whenever old 169 reads 1, the cell to its right is 1. On the boundary source this
guard holds over all 8,386 instruction frames, with a right-hand 1-run of constant
at least 23, and on the blank prefix.

### 3. Shared helper again: 238 → 237 (state 235)

Delete state 235 and merge it into 98: `139/1, 156/1 → 1 R 98` (the only rows that
entered 235), `98/0 → 0 L 240`, and helper `240/1 → 1 L 87`. Old 98 and 235 already
had the same read-1 row. On read 0 their left contexts are disjoint (0 for 98, `11`
for 235), and the changed helper `240/1` separates the two roles.

| Old row | Left | New path | Steps |
| --- | --- | --- | ---: |
| `98/0` | 0 | 98 → 240 → 176 → 113 | 3 |
| `235/0` | 11 | 98 → 240 → 87 → 164 → 118 → 231 | 5 |
| `240/1` | 0 | 240 → 87 → 190 → 99 | 3 |

Every intermediate write puts back the bit just read. A predecessor invariant holds
from state 95 on **every** binary initial tape, so this fold, too, needs no runtime
premise. The clock is `τ(t) = t + 2a + 4b + 2c` for the three exceptional rows, with
`t ≤ τ(t) ≤ 5t`.

## Verification

| Check | Result |
| --- | --- |
| Direct unbounded runtime of **this table** on its source: Source 106, and replayed by the intake with Source 103's unchanged checker ([receipt](evidence/runtime237_intake.json), [cases](evidence/runtime237_intake_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: **8,386** guarded cases, **2,261,369** symbolic rules, all 474 rows, minimum instruction duration 13 |
| Exact blank startup, sparse and dense ([code/boot.py](code/boot.py), [record](evidence/boot237_intake.txt)) | the complete frame after **409,835** steps |
| Source equivalence of the reparenthesized source (Source 103) | the control graph is equal at all 6,455 leaves and 8,386 guarded edges; the source data and seed are identified with the pinned Lean definitions; the intake's fresh replay passed 8/8 checks |
| Block simulations ([code/check_blocks.py](code/check_blocks.py)) | all eleven exceptional paths above, re-derived from the literal tables |
| Rebuild ([code/build237.py](code/build237.py)) | the inherited table, byte for byte, from the [238-state candidate](../candidate-combined238/README.md) |

The runtime checker is an induction engine, not a test over sample values. Its cases
quantify over all natural values of the nine registers, an arbitrary extra gap, an
arbitrary first spare and an arbitrary finite list of further spares. Unary runs and
spare lists are crossed by induction, using block lemmas re-proved from the literal
table. Its 4,000-rule cap bounds the construction of a proof, not the machine's
running time.

The startup frame is head −5, marker −6, header 176, 351 one-cells, logical
registers `(3,0,0,0,3,0,0,0,0)` and 167 spare blocks of value 1, with every other
cell 0. The 240 and boundary tables reach it in 409,691 steps. The delayed erasure
adds exactly `4·18 + 2·12 + 4·6 + 8·3 = 144` steps, from its exceptional visit counts.
The 235 fold's exceptional rows are not visited during startup.

Further fold searches on this table found nothing. The intake re-ran
Source 106's discovery search and Source 103's all-tape fold search on it and on two
variants, as recorded in the
[batch 173 reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-173.md#can-the-ideas-be-combined-below-237).
These are bounded searches, not lower bounds.

See the [mathematical reconciliations](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-172.md)
([batch 173](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-173.md),
[batch 174](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-174.md)),
the fresh-run records ([172](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake172-fresh-replay.json),
[173](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake173-fresh-replay.json))
and the [reproduction instructions](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-173-reproduction.md).
The calibration of the register source to ZF/ZFC refutation is the
[Lean-checked one of the 240 candidate](../calibrated_rotation240.md). It applies here
through Source 103's source equivalence.

## Exact files and attribution

| File | Meaning |
| --- | --- |
| [zfc_composed237.tm](zfc_composed237.tm) | Canonical table: states 0–236, start 0, dispatcher 84, halt 237. |
| [zfc_composed237_old.tm](zfc_composed237_old.tm) | Inherited labels: start 95, dispatcher 96, halt 254. |
| [sites_logical.json](sites_logical.json) | Exact 6,455-leaf reparenthesized source (224 distinct subtrees). |
| [renumbering.json](renumbering.json) | Canonical state bijection. |
| [construction.json](construction.json) | Every stage from the 240 table: hashes, deleted states and row edits. |
| [provenance.json](provenance.json) | Deliveries, placements, reconciliations and the intake's fresh checks. |
| [ingredients/](ingredients/) | `rotation240`, `boundary240`, `boundary239` and `delayed239` tables (inherited labels). |
| [code/](code/) | `build237.py`, `check_blocks.py`, `make_construction.py`, `boot.py`. |
| [evidence/](evidence/) | The intake's runtime receipt with per-case records, and its startup record. |

Canonical SHA-256:
`7eda1da1fcda629cae86d22b01d3faf419552cf04ed4179f0c045ad0adf2c1a6`.
Inherited SHA-256:
`a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a`.
Source SHA-256:
`7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6`.
Each non-comment row is `state read write direction next_state`.

The original calculus, program and 254-state construction are credited to Mira-Cult,
upstream verification to Jeff Ketchersid, and the compiler framework to Andrew James
Wade. ProveIt and its earlier incoming reports keep credit for the reductions to 240.
The source boundary saving belongs to Source 103, the delayed erasure to Sources 101
and 102 (found independently), and the 235 fold to Source 106. Source 110
independently certified the last. See [ATTRIBUTION.md](ATTRIBUTION.md). The inherited
licenses and notices are kept under `licenses/`, without relicensing.
