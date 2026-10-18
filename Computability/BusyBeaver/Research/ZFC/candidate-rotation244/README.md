# Loop-rotation 244-state candidate

This binary, single-tape machine has **244 working states**, including initialization, and one separate halt state. It starts in state 0 at head 0 on an all-zero two-way infinite tape. Every transition moves left or right.

The ordinary mathematical proof supports **ZFC ⊢ (¬Halt(QT244) ↔ Con(ZFC))**. The saving comes from rotating a transfer loop in the proof-search source and changing its binary decoder. It is different from the local fold used by the already checked [compensated244 machine](../candidate-compensated244/README.md).

```text
Before:                       After:
while X > 0:                  repeat:
    X := X - 1                    N := N + 1
    N := N + 1                    if X = 0: exit
N := N + 1                        X := X - 1
```

For arbitrary natural entry values N and X, both source blocks terminate after exactly `3X+2` source instructions. They increase N by X+1, clear X and preserve the other seven registers. The [source proof](proof/rotation.tex) checks all 8,385 surrounding control-flow edges and excludes outside entry into the loop interior. The resulting source has 6,459 leaves and 8,390 guarded cases.

In inherited labels, delete state 26 and change only rows 12/0, 12/1 and 17/1. The two rows at 12 exchange targets 17 and 18; row 17/1 becomes `0 L 20`. All 485 other retained rows are unchanged. These labels are not the canonical state numbers.

Root's fresh seven-job Python replay passes exact reconstruction, source context, sparse/dense initialization, frame closure, affine runtime, finite literal fixtures and the complete expanded runtime. The expanded replay checks **8,390 cases and 2,312,438 symbolic rules** in **518.026 seconds**. It covers 487 rows; inherited row `(27,1)` is unused and retained to keep the table total. State 27 itself remains used and counted.

The universal runtime contract permits nine arbitrary natural primary registers, gap `64+n`, and every nonempty finite spare suffix of arbitrary natural values. It checks positive progress and complete tape endpoints. The separate finite regression performs 6,470,964 transitions; those fixtures corroborate the unbounded induction argument.

The blank machine reaches the exact root frame after **407,931 transitions**: inherited dispatcher 96, head −5, marker −6, header 176, span 181, logical seed `(3,0,0,0,3,0,0,0,0)`, 167 spare ones and 351 one-cells, with zero elsewhere. This is the routed245 root frame reached 16 transitions later. A finite startup check does not itself establish nonhalting.

| Construction | Mechanism | Deleted inherited states | Source leaves / cases | Blank prefix |
| --- | --- | --- | --- | --- |
| Routed245 | Baseline | Neither 26 nor 122 | 6,460 / 8,391 | 407,915 |
| Compensated244 | Local fold with backward-route repair | 122 | 6,460 / 8,391 | 407,951 |
| QT244 | Source loop rotation and decoder change | 26 | 6,459 / 8,390 | 407,931 |
| [Combined243](../candidate-combined243/README.md) | Both changes, with the transfer hypotheses checked | 26 and 122 | 6,459 / 8,390 | 407,967 |

The exact QT244 consistency endpoint has an ordinary proof and fresh Python certificate replay. **Its complete Lean consistency endpoint remains open.** The [relative Lean comparison](../combined243_simulation.md) checks the rotated and combined tables and proves that combined243 halts exactly when QT244 does. It does not close QT244's calibrated source bridge. The closed [compensated244 endpoint](../compensated244_binary.md) concerns a different table, and the internal [PA calibration](../pa_internalization.md) remains open.

| Artifact | Meaning |
| --- | --- |
| [zfc_rotation244.tm](zfc_rotation244.tm) | Canonical 488-row table: working states 0–243, start 0, dispatcher 87, halt 244. |
| [zfc_rotation244_old.tm](zfc_rotation244_old.tm) | Same machine in inherited labels: start 95, dispatcher 96, halt 254. |
| [renumbering.json](renumbering.json) | Exact bijection. |
| [Logical sites](sites_logical.json), [physical sites](sites_physical.json) | Actual right-associated source and register permutation. |
| [construction.json](construction.json), [boot.json](boot.json) | Exact construction and complete startup frame. |
| [Ordinary comparison](proof/ordinary-comparison.md) | Independent source and combination argument; its original review scope remains explicit. |
| [Primary verification](evidence/primary-verification.json), [existing-evidence review](evidence/primary-review.json) | Actual seven-job replay and independent metadata review. |
| [provenance.json](provenance.json) | Exact selected inputs and source identities. |

Canonical SHA256: `91ff0ff2dfe9155548d21405615934b46784c5e3cb850bbf056682d02b203790`. Inherited SHA256: `0160caaf5d6db52eb7eb97a76cb04db4b424eb2bc0d58617818a6c7c6a1fe776`. The common routed245 inherited baseline is `f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`.

The report arrived in commit `d91a27b462cbf7fdc6537739775fd192b06fb769`, against ProveIt `fd1adfa19f8fe8da41444e3fa43b89a59d891067` and inherited upstream `c132d7eae8158cd3a9850ea3eb7251158c3dd821`. Placement `5513e77ff1` preserves 1,007 ancillary files plus 37 archive-only members. The [collection host](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md) retains the formalism, grammar, joint-source and rejected-NIP research; the complete original package remains recoverable from the committed arrival. Its unused auxiliary whole-frame wrapper has a preserved indentation defect; the successful primary replay uses `check_runtime.py --expanded` instead.

Credits follow the delivery: Mira-Cult's original calculus/program, Jeff Ketchersid's verification, Andrew James Wade's compiler, ProveIt's preceding reductions, and the incoming contribution's concrete rotation and research. It was prepared for Vladimir Reshetnikov's repository; no additional individual author is inferred. Loop rotation and the Tarski–Bernays basis are established ideas. Inherited licenses remain attached to the complete intake. No absolute consistency, unconditional nonhalting, minimality or two-sided independence from consistency alone is claimed.
