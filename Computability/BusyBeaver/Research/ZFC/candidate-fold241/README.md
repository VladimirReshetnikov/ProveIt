# Predecessor-bit 241-state candidate

This binary, single-tape machine has **241 working states**, including
initialization, plus one separate halt state. It starts in state 0 at head 0
on an all-zero two-way infinite tape; every transition moves left or right.
Its 482 transition rows are in [zfc_fold241.tm](zfc_fold241.tm).

The construction in commit `8c41b1fb7d` reduces the maintained
[combined243 machine](../candidate-combined243/README.md) in two stages.
The primary 242-state fold merges inherited state 27 into 15. The companion
then merges inherited state 39 into 17. The direct construction deletes
27 and 39 and changes eight retained rows; all other retained rows are
unchanged. The logical source is the same 6,459-leaf QT program.

The ordinary mathematical argument gives halting equivalence with
combined243 and inherits its ZFC consistency interpretation. **The complete
241-state Lean consistency theorem and the internal PA equivalence remain
open.** The separately checked
[compensated244 theorem](../compensated244_binary.md) remains the closed
external Lean baseline. This candidate does not assert unconditional
nonhalting, absolute consistency, minimality or two-sided independence from
mere consistency.

## How the last state is saved

Every entry into old state 17 writes a 1 immediately left of the head.
Every entry into old state 39 writes a 0 there. The new machine uses that
existing bit to distinguish the two roles after merging their controls.

| Old control | Current bit | Left bit | New control path | New steps |
| --- | --- | --- | --- | --- |
| 17 | 0 | 1 | 17 → 106 → 92 → 107 → 125 → 25 | 5 |
| 17 | 1 | 1 | 17 → 37 → 55 → 20 | 3 |
| 39 | 0 | 0 | 17 → 106 → 93 → 57 | 3 |
| 39 | 1 | 0 | 17 → 37 → 25 → 69 | 3 |

Each path matches one old transition, including its final head position and
whole tape. Every other old transition matches one new transition through
the state map. The invariant follows from the complete incoming-transition
inventory and holds at inherited start 95 for every head and tape. Positive
block lengths and preservation of halting therefore give both directions of
halting equivalence. The ordinary proof includes infinite-support tapes;
the pending Lean specialization uses the repository's finite-support `Core`
tapes, which suffice for blank input.

Relative to the primary242 machine, the exact clock is
`new = old + 4·visits(17,0) + 2·(visits(17,1)+visits(39,0)+visits(39,1))`.
The 407,979-step old startup visits these rows 15, 3, 132 and 55 times,
giving 440 additional transitions and a **408,419-step** new startup.
The initialized tape has 351 one-cells and zero elsewhere, head −5,
marker −6, header 176, logical registers `(3,0,0,0,3,0,0,0,0)` and
167 spare blocks of value 1.

## Evidence and formalization

Root freshly replayed both local checks, the exact sparse/dense blank startup,
133 concrete instruction instances, and the complete unbounded runtime
certificate: **8,390 cases, 2,319,442 symbolic rules, all 482 rows**, with
minimum instruction duration 13. Every generated case record matches the
delivered evidence. The same run refreshed all three preceding 242 variants
and combined243, for 19 successful substantive jobs in total. See the
[actual replay](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake168-fresh-replay.json)
and [reproduction instructions](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-168-reproduction.md).
This is executable mathematical evidence; it is separate from a Lean theorem.

The two reductions have been reviewed independently at source level. Lean
drafts use `PositiveBlockBisimulation` with a noninjective state map, the old
invariant and the four short paths above. The shared source calibration,
Rotation244 runtime, startup and frame theorems are already checked. Complete
decoder-site coverage and the final binary composition are still being
checked; the new relative folds then transfer that result to 241 states.
The [PA work](../pa_internalization.md) is a further obligation, and reuses
the same logical source and existing interpretability library.

## Exact files and provenance

| File | Meaning |
| --- | --- |
| [zfc_fold241.tm](zfc_fold241.tm) | Canonical table: working states 0–240, start 0, dispatcher 85, halt 241. |
| [zfc_fold241_old.tm](zfc_fold241_old.tm) | Same table in inherited labels: start 95, dispatcher 96, halt 254. |
| [renumbering.json](renumbering.json) | Exact canonical relabeling. |
| [direct-construction.json](direct-construction.json) | Two deletions and eight edits relative to combined243. |
| [provenance.json](provenance.json) | Delivery, exact selected inputs and replay evidence. |

Canonical SHA256:
`c5278eaf0561cd12d676b3e9c030ffe46d5bc7ec94d29d705dee31a72ea95158`.
Inherited SHA256:
`1fa8526c3c971d5a48868599eaed890f614c5a79256e51622d3e32a64229f3a3`.
Each noncomment row is `state read write direction next_state`.

The [source73 intake note](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-168-source-73.md)
contains the full proof reconciliation and recovery instructions. Its
[source72 predecessor](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-168-source-72.md)
preserves all three alternative242 folds. The companion uses the primary
15/27 fold; the three242 alternatives are not interchangeable patches.
The original manuscripts, PDFs and package layouts remain recoverable from
their committed delivery archives.

The original calculus and program are credited to Mira-Cult, upstream
verification to Jeff Ketchersid, and the compiler framework to Andrew James
Wade. ProveIt retains credit for earlier source, routing, initialization and
formalization work. The compensated244, QT rotation and neutral-edit research
retain their incoming-package attribution. The new17/39 fold belongs to
the incoming241 companion; no unsupported personal author is inferred.
Original license and source notices are retained under `licenses/` without
relicensing inherited material.
