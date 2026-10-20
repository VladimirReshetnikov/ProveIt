# Rel224: a 224-state binary Turing machine

This directory contains the final machine module for the ProveIt ZFC research contribution. The machine has **224 working states**, two tape symbols, one tape extending infinitely in both directions, and a distinguished halting state. It starts in state 0 on the all-zero tape. Every working state has both transitions; each transition writes a bit and moves one cell left or right.

The final construction applies a contextual state fold to the fixed **Rel225** input. The companion source/theory construction explains why that input searches for an inconsistency in a calculus equiconsistent with ZFC. This module independently checks the final machine transformation, complete blank startup, source successor closure, label maps, and every unbounded binary instruction case.

## Main artifacts

| File | Purpose |
| --- | --- |
| `results/candidate224.tm` | Canonical final table: working states 0 through 223, halt 224, start 0. |
| `results/candidate224.k.tm` | The same table with inherited K labels, facilitating comparison with the parent. |
| `results/candidate224.legacy.tm` | The same table with the legacy labels used by the retained symbolic runtime engine. |
| `results/renumbering224.json` | Explicit bijections between the three label systems. |
| `results/sites.json` | The 4,799-leaf source program, unchanged by the final fold. |
| `results/construction224.json` | Construction recipe, counts, and artifact SHA-256 hashes. |
| `results/independent224.json` | Standalone whole-tape fold proof, complete blank frame, and rejected tamper controls. |
| `results/universal224.json` | Full unbounded binary-runtime proof receipt. |
| `results/universal224_cases.json` | All 6,238 guarded source-instruction derivations. |

A transition line has five fields: `state read write direction next_state`. The first line declares the start state, for example `#! start 0`. Halting states have no outgoing rows. Thus the canonical table's 448 transition lines represent 224 working states; state 224 is the additional terminal control.

## Reproduction

Python 3 and its standard library are sufficient. Run from this directory, or use absolute script paths:

```sh
python build224.py --output /tmp/rel224-replay
python check224.py --results /tmp/rel224-replay
python runtime224.py --results /tmp/rel224-replay
```

The first command reconstructs all tables and their maps from the pinned parent. The second freshly verifies the four exceptional whole-tape blocks, all ordinary rows, complete blank startup in both K and canonical labels, source successor closure, and three tamper controls. The third freshly rederives every unbounded instruction case using the two retained engine modules in `vendor/`.

Without `--output` or `--results`, the scripts use this directory's `results/`. To audit the shipped runtime proof data's integrity and coverage without freshly rederiving it, use:

```sh
python runtime224.py --audit-stored
```

The runtime proof requires assertions to be enabled. Its 4,000-step symbolic derivation limit bounds proof construction; it does not bound concrete register values, spare-list length, or concrete execution time.

## The state saving

The parent has two ordinary prefix-decoder states:

| Parent state | On 0 | On 1 | Bit immediately to the left |
| --- | --- | --- | --- |
| 157 | `0 R 90` | `1 R 86` | 0 |
| 191 | `0 R 155` | `1 R 182` | 1 |

The predecessor facts follow directly from the complete incoming-transition lists. Every transition into 157 writes 0 and moves right; every transition into 191 writes 1 and moves right. Neither is the initial state. The facts therefore hold from the common initial state on **every binary initial tape**, with any initial head position.

Delete state 191, redirect its incoming transitions to 157, and replace the retained state's two rows by:

```text
157 0 0 L 67
157 1 1 L 148
```

All other rows remain identical after the state renaming. Existing helper rows inspect and preserve the predecessor bit, then return to the current bit. The exact state sequences are:

| Parent transition | New state sequence | New steps | Endpoint |
| --- | --- | --- | --- |
| 157 / 0 | 157 → 67 → 151 → 90 | 3 | Old head + 1, state 90 |
| 157 / 1 | 157 → 148 → 186 → 86 | 3 | Old head + 1, state 86 |
| 191 / 0 | 157 → 67 → 152 → 159 → 118 → 155 | 5 | Old head + 1, state 155 |
| 191 / 1 | 157 → 148 → 173 → 182 | 3 | Old head + 1, state 182 |

Each block accesses only the original head cell and the cell immediately to its left, and restores both exactly. The entire exterior tape remains arbitrary and untouched. The remaining 446 parent rows commute with the state map in one step. Consequently every parent step is simulated by a positive block of one, three, or five final-machine steps, with no interior halt and exactly the mapped whole-tape endpoint. This yields halting equivalence for the common start on every binary initial tape.

The important source change occurs before this fold: the canonical relational binder representative creates the opposite predecessor tags required for the two decoder roles. The companion source construction provides that calibration; this final local proof does not assume that finite test runs establish nonhalting.

## Verification results

- **Final census:** 224 working states, 448 rows, all working states reachable in the transition graph.
- **Source:** 4,799 leaves, 6,238 guarded cases, maximum depth 38, maximum zero run 6; every successor resolves without a nonzero unread suffix.
- **Local theorem:** 446 one-step blocks, three three-step blocks, one five-step block; exact whole-tape equivalence and positive progress.
- **Blank startup:** exactly 409,835 steps to the complete canonical frame. The tape contains 351 one-cells, with every other cell zero; the final head is at -5. Logical registers are `(3,0,0,0,3,0,0,0,0)`, the extra gap is 117, and the spare list contains 167 copies of 1.
- **Universal runtime:** all 6,238 guarded cases pass, covering all 448 literal rows. The proof uses 1,503,342 symbolic steps, with at most 403 symbolic steps in a case and minimum actual case duration 13.
- **Negative controls:** a wrong predecessor tag, a broken shared helper, and an incorrect retained row are independently rejected.

These are executable ordinary mathematical proofs and independently checked finite identities. This contribution does not add a proof-assistant kernel endpoint. The inherited theory calibration and the newly constructed source bridge are recorded by the companion package.

## Exact identities

```text
Canonical table SHA-256:
6361b0b29c2e0485bf8cf025dcf2606c2fac071f3f6e24fbde04016466d92168

K-label table SHA-256:
f886dd8d11e9705c5315140f68d5ae2f26c80afb015e08074c7e3da1414fa37f

Legacy-label table SHA-256:
e8467b9745c7a05860797a209ed05ce0b41b72a44d96f00aad43630a589ccc2f

Source SHA-256:
309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878

Unbounded runtime case-array SHA-256:
76d28d291b1c4a2087af7123417720b431d87c27b8d1a6e953c54ac7deca8e64
```

## Attribution and dependencies

The fixed Rel225 input comes from the companion source construction on ProveIt commit `ad8cbe8249445f43408617e88a0edb668b00248d`. The inherited state map and both generic runtime-engine modules are copied byte for byte from the ProveIt Source124 portable K225 packet. Their exact hashes are checked during reproduction. The construction script, standalone final-fold checker, runtime adapter, and final machine tables in this module are part of this contribution.
