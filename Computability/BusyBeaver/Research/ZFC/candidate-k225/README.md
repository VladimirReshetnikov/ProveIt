# K-theory 225-state candidate

This binary, single-tape machine has **225 working states**, including initialization, plus
a separate halt state. It starts in state 0 at head 0 on an all-zero two-way infinite tape.
Every transition moves left or right. The complete 450-row table is [zfc_k225.tm](zfc_k225.tm).
It was the smallest known candidate until the [224](../candidate-k224/README.md) (Source 125),
and it is **the smallest with a kernel-checked endpoint**: its Rocq theorem passes `coqchk`.

It is Source 124 of the ZFC closure-kernels host (arrival `680f058702`; see the
[batch 178 reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-178.md)).
It descends from Elliot Glazer's [k230-rocq](https://github.com/elliotglazer/k230-rocq) (commit
`3142e4d`), whose machine searches a compact set theory K proved equiconsistent with ZFC. An
ordinary mathematical proof, formalizable in ZFC, establishes

  ZFC ⊢ (this machine does not halt from the blank tape ↔ Con(ZFC)).

It composes three parts:

- the unbounded runtime certificate for this table on its own source;
- the exact blank startup;
- the delivered source and fold certificates, back to k230's source, whose Rocq theorem
  supplies the calibration.

**Rocq endpoint.** `K225F.CorrectDense225.tm225_halts_iff_ZFC_inconsistent` states
`Dense.halts dense_tm Dense.c0 ↔ StandardZFC ⊢TC ⊥` for the literal table above. It is closed
under the global context, and `coqchk` independently rechecked it (`PASS_CLOSED_KERNEL`,
2026-10-19). It extends Source 123's K226F extension; the sources, receipts and toolchain notes
are in [k225-formal/rocq](../k225-formal/rocq/README.md). The Lean endpoint is in progress
([k225-formal](../k225-formal/README.md)): the source equivalence (layer A) is proved, and the
machine layer is under way. No proof internal to PA exists. No absolute consistency,
unconditional non-halting, minimality, or two-sided independence from bare consistency is
claimed.

## How the states are saved

K230 has 230 states. This table deletes K230 states 79, 140, 175, 208 and 229 (in K labels):

| Step | Saving | Origin |
| --- | --- | --- |
| 230 → 229 | loop rotation, fold 79 into 63 | ProveIt's 240-state step (`e5c2b3337e`), transferred in [candidate-k228](../candidate-k228/README.md) |
| 229 → 228 | delayed erasure, fold 140 into 71 | Sources 101/102, transferred in candidate-k228 |
| 228 → 227 | 49-atom source layout; split K175 by the bit behind the head | Source 117 |
| 227 → 226 | rotation at 210/177; fold 208 into 76 | Source 117 |
| 226 → 225 | four rotations; fold 229 into 152 | Source 124 |

In state-count terms the 225 is 49 engine states + 188 distinct interior source nodes − 12
tag-shared roles. Against K230 (51 + 189 − 10), that is two engine states, one source node
and two extra sharings.

**The last step.** Four closed source reassociations, in K labels right 169/136, right
170/169, left 169/154 and right 159/118, expose helper states 159 and 170. Zero-tagged state
229 then merges into one-tagged state 152, with `152/0 = 0 L 159` and `152/1 = 1 L 170`.
State 152 is also the helper of the earlier 208 → 76 fold. That use survives: an inductive
bit invariant shows that its left-moving arrival from `76/0` also has a 1 to its left, so
the merged state behaves there exactly as the old 152 did.

## Verification

| Check | Result |
| --- | --- |
| Direct unbounded runtime of **this table** on its own source, with Source 103's checker ([receipt](evidence/runtime225.json), [cases](evidence/runtime225_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: **6,656** guarded cases, **1,608,136** symbolic rules, all 450 rows, minimum instruction duration 13 |
| Exact blank startup, sparse and dense ([code/boot.py](code/boot.py), [record](evidence/boot.txt)) | the complete dispatch frame after **409,835** steps |
| Finite screen on every leaf and both decrement guards ([code/screen.py](code/screen.py), [record](evidence/screen.txt)) | 0 failures |
| Delivered canonical table vs the checked inherited-label table ([code/make_inherited.py](code/make_inherited.py)) | the same machine (BFS-canonical forms equal) |

These checks are the intake's own. The rule count equals Source 124's receipt. The runtime
checker is Source 103's `check_literal_runtime.py`, adapted as for the
[228](../candidate-k228/README.md): no source hash pin, and the case count computed from the
supplied source. Its receipt records the SHA-256 of this page's
`zfc_k225_old.tm` and `sites_logical.json`.

**Looking further.** The plain and helper fold searches find no further fold on this table. A decomposed
search over rotation chains (per-pair helper sub-goals, then composition) was paused before
it finished; see the
[batch 178 reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-178.md#the-intakes-search-below-225).
These are bounded searches, not lower bounds.

## Exact files and attribution

| File | Meaning |
| --- | --- |
| [zfc_k225.tm](zfc_k225.tm) | Canonical table as delivered: states 0–224, start 0, dispatcher 83, halt 225. |
| [zfc_k225_old.tm](zfc_k225_old.tm) | fold241 inherited labels (start 95, dispatcher 96, halt 254), the table the checkers ran on. |
| [sites_logical.json](sites_logical.json) | Exact 5,121-leaf source (211 distinct subtrees, depth 38, zero run 6). |
| [ingredients/](ingredients/) | Delivered legacy- and K-label tables, the delivered renumbering, and the label compaction. |
| [code/](code/) | `make_inherited.py`, `boot.py`, `screen.py`, the adapted runtime checker and `setup_checkers.sh`. |
| [evidence/](evidence/) | Runtime receipt with per-case records, startup and screen records. |

Canonical SHA-256 `f5d69a16a0324c69c8c6c407dbf18abcccf0e2d2a2283d5101ebc4591964140c`; inherited
`b6891e5571b00a45ddbc8a18c956170e6f83ac67748bdcd0f517cfbdacd0e9c8`; source
`86b28af08e646eb7da8b822f63a03173ef5182e5a2ebc0404008e1b2af41b55b`.

The theory K, its consistency proofs, the K source and the 230-state machine are Elliot
Glazer's. The 49-atom layout, the K175 split and the 208 → 76 fold belong to Source 117. The
final four rotations and the 229 → 152 fold belong to Source 124. The two engine savings are
ProveIt's and Sources 101/102's, as on the 228 page. See [ATTRIBUTION.md](ATTRIBUTION.md).
