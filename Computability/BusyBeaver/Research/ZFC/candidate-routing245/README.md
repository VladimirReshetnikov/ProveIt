# Routed 245-state candidate

This binary, single-tape machine has **245 working states**, including all
initialization, and one separate halt state. It starts in state 0, head at 0,
on an all-zero two-way infinite tape. Every transition moves left or right.

The ordinary mathematical proof and complete executable verification support
**ZFC ⊢ (¬Halt(M245) ↔ Con(ZFC))**. Fresh replay passes all 8,391 universally
guarded instruction cases, expanded whole-tape checks, source bisimulation,
and the exact blank initialization. Independent source reviews found no
substantive blocker. **The exact 245-state Lean endpoint and the proof inside
PA remain open.** The [246-state machine](../prefix246_binary.md) remains the
closed external Lean baseline.

The first [245-state Lean unit](../table_routing245.md) now checks the exact
transition table, state numbering and 46 reusable core rows: 64 theorem
audits and 64 typed callers pass with zero warnings. Complete coverage remains
a separate obligation. The
[fast lookup](../fast_table_routing245.md) is also checked equal to the literal
machine, with two theorem audits and four typed callers.
The [exact register decoder](../program_routing245.md) now also passes
11 theorem audits and 13 typed callers: its shared representation unfolds
to all 6,460 instruction leaves and preserves consumed-pointer semantics
for arbitrary register values. The
[complete source bisimulation](../bisim_routing245.md) now checks all 3,013
certificate entries and proves halting equivalence with the original program
for every initial register function at empty pointers. Its 97 production
modules pass 104 theorem probes and 201 typed callers, with zero warnings.
Complete decoder coverage still needs its own Lean proof.
The [local register operations](../routing245_local.md) now pass 27 theorem
probes and 29 callers: pulse, marking, increment and both decrement branches
are checked for arbitrary values and finite contexts, preserving the full tape.
The [symbolic execution and runtime proofs](../routing245_execution.md) pass
59 theorem probes and 62 callers, with zero warnings in the selected runs.
They prove halting equivalence under explicit complete-coverage and initial-frame
premises, retaining the entire tape in a new 64-cell dispatch frame.
The [complete blank-start proof](../routing245_bootstrap.md) now checks all
407,915 transitions and supplies that exact initial frame, including the
logical seed and 167 spare blocks. Its eleven modules pass 80 probes and
111 callers with zero warnings. Complete coverage and the final binary
composition remain before the closed endpoint.

| Artifact | Meaning |
| --- | --- |
| [zfc_routing245.tm](zfc_routing245.tm) | Canonical table: working states 0–244, start 0, dispatcher 88, halt 245; 490 rows. |
| [zfc_routing245_old.tm](zfc_routing245_old.tm) | Equivalent original labels: start 95, dispatcher 96, halt 254. |
| [renumbering.json](renumbering.json) | Exact bijection of the two tables. |
| [grammar.json](grammar.json) | The successful 128-rule source grammar. |

Each noncomment table row is `state read write direction next_state`.
The canonical table identity is
`17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`.
These four implementation inputs are copied byte-for-byte from the delivery.

The saving comes from optimizing the source grammar, special entry routes,
and scanner together: 117 framework roles plus 128 grammar roles. The source
theory and all eight axiom-construction rows are preserved. Maximum source
depth is 51; the complete runtime frames use header distance 64+n for every
natural n, arbitrary primary registers, and any nonempty finite spare suffix.

The blank prefix takes **407,915 transitions** and reaches the same logical
seed as the verified 246 machine: `(3,0,0,0,3,0,0,0,0)`, head −5, header 176,
and 167 spare blocks of value one. All 351 one-cell coordinates are checked.
The expanded runtime certificate has 2,312,645 symbolic rules covering all
490 rows. The separate 8,385 literal fixtures are finite regression checks.

The original solution and compact calculus are attributed to Mira-Cult,
verification to Jeff Ketchersid, and the compiler framework to Andrew James
Wade. ProveIt's earlier permutation/prefix machines and the new submission's
joint grammar/routing search retain their attribution. This candidate arrived
in [commit 8286787dd0](https://github.com/VladimirReshetnikov/ProveIt/commit/8286787dd0468d848db345debe304b002d7064a4),
against ProveIt `c6bf052c70bbbafba8c39370a6a2d123f57cd2c1` and upstream
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`.

The external report, proof notes, licenses and all delivered evidence are
preserved through [intake 164](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-164.md).
Its [recovery and reproduction instructions](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-164-reproduction.md)
restore the complete package and rerun verification on a disposable copy.
This directory contains maintained machine inputs, not a replacement archive.
No absolute consistency proof, unconditional nonhalting theorem, minimality
claim, or two-sided independence from consistency alone is asserted.
