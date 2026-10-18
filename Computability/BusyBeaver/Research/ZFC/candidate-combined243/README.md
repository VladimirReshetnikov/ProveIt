# Combined 243-state candidate

This binary, single-tape machine has **243 working states**, including initialization, and one separate halt state. It starts in state 0 at head 0 on an all-zero two-way infinite tape. Every transition moves left or right.

It combines the [QT loop rotation](../candidate-rotation244/README.md) with the [compensated fold](../candidate-compensated244/README.md). The ordinary argument supports **ZFC ⊢ (¬Halt(M243) ↔ Con(ZFC))**. This table was developed in the repository after reviewing both reports; neither incoming ZIP supplied a 243-state machine.

The later [submission in commit 074c76bb74](comparison-074c76bb74.md) supplies
exactly the same machine: both tables, renumbering and both source-site lists
are byte-identical. It adds a standalone local audit, explicit clock bounds
and a separate finite-algebra research proposal, with no further state reduction.

| Construction | Mechanism | Deleted inherited states | Source leaves / cases | Blank prefix |
| --- | --- | --- | --- | --- |
| Routed245 | Baseline | Neither 26 nor 122 | 6,460 / 8,391 | 407,915 |
| Compensated244 | Local fold with backward-route repair | 122 | 6,460 / 8,391 | 407,951 |
| QT244 | Source loop rotation and decoder change | 26 | 6,459 / 8,390 | 407,931 |
| Combined243 | Both changes, with the transfer hypotheses checked | 26 and 122 | 6,459 / 8,390 | 407,967 |

Starting from the common routed245 table, the combination deletes old states 26 and 122 and changes seven retained rows: 12/0, 12/1 and 17/1 for QT; 92/1, 104/1, 106/1 and 167/1 for compensation. It has 486 total binary rows, with 479 retained rows unchanged and no transition targeting either removed state.

The edits commute as literal patches, but that fact alone would not prove the combination sound. The [ordinary comparison](proof/ordinary-comparison.md) checks every compensation hypothesis against the rotated table: the local tape invariant, all required incoming edges, the seven whole-tape block identities, the ordinary-row classification and excluded comparison controls. None of the exceptional calculations uses deleted state 26 or the changed rows at 12 and 17. Positive finite blocks therefore preserve halting from the shared old start 95 with arbitrary head and tape. Composing with QT's source/runtime/seed argument gives the ordinary consistency calibration.

The [relative Lean theorem](../combined243_simulation.md) now checks this binary transfer. Its five units have **83 theorem probes and 39 typed callers**, all with zero warnings: two exact tables, the local invariant, seven whole-tape blocks and global simulation. It proves combined243 halting equivalent to QT244 halting on blank input and, more generally, from the shared start on arbitrary finite Core tapes and head positions. **The complete 243-state Lean consistency endpoint remains open.**

The [rotated source calibration](../source_rotation244.md) is now checked:
the rotated register program halts exactly when ZF/ZFC has a refutation, from
the established logical seed. Five source units pass 34 probes and 40 typed
callers with zero warnings. The remaining external proof must connect the
exact Rotation244 binary runtime and its blank initialization to that source
seed. The checked blank-input equivalence then transfers the result to this
243-state table; this route does not require a separate 243-state initialization
proof. Internalizing the full argument in [PA](../pa_internalization.md)
remains an additional obligation.

Root's separate complete expanded replay passes **8,390 cases and 2,314,868 symbolic rules** in **509.285 seconds**. It covers 485 of 486 rows, with only inherited `(27,1)` unused. The actual table, source, adapters and inputs are bound before and after execution. This is a Python induction-certificate replay, distinct from the relative Lean theorem.

The [quick verification](evidence/quick-verification.json) independently records the newly computed **407,967-transition** blank prefix, all 8,390 affine cases and all 8,390 finite literal fixtures totaling **6,473,394 transitions**. The root frame has inherited dispatcher 96, head −5, marker −6, header 176, span 181, logical values `(3,0,0,0,3,0,0,0,0)`, 167 spare ones and 351 one-cells, with zero elsewhere. The startup time is an actual result, not an addition of predecessor timing differences. The finite literal fixtures do not replace the expanded induction proof.

| Artifact | Meaning |
| --- | --- |
| [zfc_combined243.tm](zfc_combined243.tm) | Canonical 486-row table: working states 0–242, start 0, dispatcher 87, halt 243. |
| [zfc_combined243_old.tm](zfc_combined243_old.tm) | Same table in inherited labels: start 95, dispatcher 96, halt 254. |
| [renumbering.json](renumbering.json) | Exact bijection. |
| [Logical sites](sites_logical.json), [physical sites](sites_physical.json) | Exact QT source lists, unchanged by compensation. |
| [Ordinary comparison](proof/ordinary-comparison.md), [static comparison](evidence/static-comparison.json) | Independent original proof/locality review, preserved with its source-only scope. |
| [Quick record](evidence/quick-verification.json), [blank record](evidence/independent-blank.json) | Actual startup, affine replay and finite literal controls. |
| [Expanded record](evidence/expanded-verification.json) | Actual complete expanded runtime result and exact input bindings. |
| [provenance.json](provenance.json) | Selected table, adapter, proof and execution identities. |

Canonical SHA256: `a3860fb49d6b96e58ead6293134f246d59b3958231cb56850273c4b8a8138791`. Inherited SHA256: `4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300`. Logical source SHA256: `3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4`. Each noncomment row is `state read write direction next_state`.

The [reproduction instructions](REPRODUCING.md) recover the inherited checker and run the exact combined adapters on a fresh copy. The direct QT commands reproduce QT244. The [collection intake](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md) records the underlying reports and their broader research. The currently closed [compensated244 consistency endpoint](../compensated244_binary.md) remains a different exact artifact.

The original calculus/program, verification and compiler remain credited to Mira-Cult, Jeff Ketchersid and Andrew James Wade, with ProveIt's earlier source/routing/initialization work. The compensated fold and QT rotation remain credited to their respective incoming contributions. The combination, independent hypothesis comparison, root replays and relative Lean transport are subsequent repository work. No additional personal author is inferred; inherited licenses remain unchanged. No absolute consistency, unconditional nonhalting, minimality or two-sided independence from mere consistency is claimed.
