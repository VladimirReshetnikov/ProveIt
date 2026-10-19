# Composed 237-state candidate

This binary, single-tape machine has **237 working states**, including blank-tape
initialization, plus a separate halt state. It starts in state 0 at head 0 on an
all-zero two-way infinite tape, and every transition moves left or right. The
canonical 474-row table is [zfc_composed237.tm](zfc_composed237.tm) (start 0,
dispatcher 84, halt 237). [zfc_composed237_old.tm](zfc_composed237_old.tm) is the same
machine with inherited labels (start 95, dispatcher 96, halt 254), and
[renumbering.json](renumbering.json) is the bijection.

It is Source 106 of the
[ZFC closure-kernels host](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-173.md),
delivered on 19 October 2026 and imported in batch 173. Its status is an ordinary
mathematical argument with executable unbounded certificates, **not** a Lean or Rocq
theorem.

| Table | SHA-256 |
| --- | --- |
| `zfc_composed237.tm` (canonical) | `7eda1da1fcda629cae86d22b01d3faf419552cf04ed4179f0c045ad0adf2c1a6` |
| `zfc_composed237_old.tm` (inherited labels) | `a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a` |
| `sites_logical.json` (register source) | `7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6` |

## Construction

It starts from the [combined 238-state candidate](../candidate-combined238/README.md):
the boundary source and the delayed-erasure fold, which saved states 218 and 169. It
then saves a third state, deleting 235 and merging it into 98:

| Row | 238 | 237 |
| --- | --- | --- |
| `98/0` | `0 R 113` | `0 L 240` |
| `139/1` | `1 R 235` | `1 R 98` |
| `156/1` | `1 R 235` | `1 R 98` |
| `240/1` | `1 R 99` | `1 L 87` |

The rows `235/0 = 0 R 231` and `235/1 = 1 R 16` are deleted, and the other 470 rows
are unchanged. As with the delayed erasure, a helper row (`240/1`) changes together
with the merge. [code/build237.py](code/build237.py) rebuilds the inherited table from
the 238 table and checks its hash.

Source 106 proves the fold for **every** initial tape at state 95. An inductive
predecessor invariant supplies the guards of three exceptional blocks of 3, 5 and 3
steps, and every intermediate write preserves the bit already present. The fold needs
no register-frame premise. Its local proof is in the placed package
(`code/106-fold237-verification-verify_237.py` and
`data/106-fold237-sections-fold237.tex` in the host).

## Verification

| Check | Result |
| --- | --- |
| Source 106: direct unbounded runtime, local fold, startup | 8,386 cases, 2,261,369 rules, all 474 rows; invariant on 120,448 cases; startup of 409,835 steps |
| **Intake replay**: Source 103's runtime checker, unchanged ([receipt](evidence/runtime237_intake.json), [cases](evidence/runtime237_intake_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: 8,386 cases, **2,261,369** rules, all 474 rows, minimum duration 13 |
| **Intake replay**: exact blank startup ([code/boot.py](code/boot.py), [record](evidence/boot237_intake.txt)) | the full initial frame after 409,835 steps; the fold's rows are not used |
| Intake rebuild from the 238 table | byte-identical inherited table |

The [batch 173 reproduction note](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-173-reproduction.md)
also records the intake's search for a **fourth** saving. Source 106's discovery search
and Source 103's all-tape fold search were both run on this table and on its variants
with delayed-erasure targets 12 and 142. They found nothing.

## Status

The argument composes Source 103's source certificate, the inherited calibration
([`CalibratedRotation240`](../calibrated_rotation240.md)), and the binary simulation
and startup checks above.

**What is claimed.** An ordinary mathematical proof, formalizable in ZFC, that this
machine fails to halt from the blank tape if and only if ZFC is consistent.

**What is not claimed.**
- No Lean or Rocq theorem for this table, and no internal PA proof.
- No minimality.
- No absolute consistency, unconditional non-halting, or two-sided independence from
  bare consistency.

## Attribution

As for the 238-state candidate: the original calculus, source and machine remain
credited to Mira-Cult; verification to Jeff Ketchersid; the compiler framework to
Andrew James Wade; the reductions to ProveIt and its incoming reports. The delayed
erasure is credited to Sources 101 and 102, and the source boundary to Source 103.
The 238 composition was found independently by the batch-172 intake and by
Sources 104–109. The 235 → 98 fold and the 237 table are Source 106's. The inherited
notices are under [licenses/](licenses/).
