# Loop rotation and the compensated fold

The new rotation has a sound ordinary source argument and can be combined with the compensated fold to obtain a concrete 243-working-state construction. The combination requires transporting the compensation proof to the rotated table; disjoint edited rows alone would not establish it. The required locality checks succeed. This review does not claim a new Lean endpoint, PA theorem, or fresh execution of the delivered checkers.

## What changes

The new packet changes the source program. At address `011`, the four leaves implementing “while X is positive, decrement X and increment N; then increment N” become three leaves implementing “increment N; test/decrement X; repeat when positive.” For arbitrary natural entry values `(N,X)=(a,b)`, both terminate after exactly `3*b+2` source instructions at `(a+b+1,0)` and preserve the other seven registers. The positive three-instruction block returns to its entry with `(N+1,X-1)`; the zero two-instruction block exits with `(N+1,0)`. Natural-number induction supplies termination. There is no reachable-register or consistency assumption.

My separate finite CFG parser verifies every one of the 8,385 surrounding edges, exact zero-padding and break/continue destinations, the sole outside entry `(old site2, zero)` to site6, and the halt correspondence 6,324→6,323. The source therefore has 6,459 leaves and 8,390 guarded cases. No outside edge enters an interior loop instruction. These checks support the stated all-natural-register source equivalence at the program root.

The physical rotation deletes old state 26 and changes `(12,0)`, `(12,1)`, and `(17,1)`. The packet's canonical dispatcher is 87, whereas compensated244's is 88: edits must use inherited labels, not mix canonical numberings. The old 245 table in this packet is byte-identical to the maintained Routing245 table. Canonical and inherited rotation tables agree under the delivered renumbering.

The compensated fold leaves the source program unchanged. It deletes old 122 and changes `(92,1)`, `(104,1)`, `(106,1)`, and `(167,1)`, matching complete binary configurations at positive two-clock block endpoints. Its proof depends on a local tape invariant rather than the QT source loop identity. These are different state savings.

## Why the combination works

Apply both literal patches to their common old 245 table. The operations commute and leave exactly 243 working labels and 486 total binary rows. Seven retained rows change and 479 retained rows are unchanged; deleted labels are 26 and 122. No transition targets either deleted label. These are static table facts, not an execution result.

Use the rotated 244 table as the OLD machine and the combined 243 table as the NEW machine in the existing compensation argument. The relation is equality of full configurations after inserting the missing old 122 state, together with the old-side local invariant and exclusion of old 92 from paired endpoints. Halt agrees under the state embedding.

The invariant is unchanged: at old 68 and old 167 the cell immediately left is one; at old 81 a left one implies a second one two cells left. All incoming rows to 68 and 167 still write one and move right. The only incoming rows to 81 remain `(68,1)` and `(123,0)`, with exactly their original actions. Initial state 95 satisfies the invariant vacuously for arbitrary head and tape. Its one-step and arbitrary-duration induction proofs therefore transfer.

Every transition row named in the seven checked compensation block calculations is unchanged on the corresponding side after the QT patch. The cases at 104 and 106 retain old/new clocks 2/4 or2/2; 167 retains 2/2; 81 retains 2/2 or 6/4. The last case still erases exactly the two specified cells, with both endpoints agreeing on the whole tape and head. No local calculation uses deleted 26 or the changed 12/17 rows.

All incoming rows to 92 and 122 are also unchanged by QT. Outside the exceptional entries and excluded92, corresponding single steps agree and cannot end at 92 or 122. The own static checker verifies this universal finite row property for every combined state/read pair. The seven block endpoints remain 25, 66, 24, 107, 2, all distinct from 92. Thus the same ordinary positive-block simulation applies, with both clocks strictly positive and every intermediate block finite.

Consequently the rotated 244 and combined 243 machines have equivalent halting from shared state 95 with the same head and arbitrary tape. The existing Lean framework represents finite-support tapes; the ordinary transition argument also works for function tapes. Starting blank is included. Composing this with the new packet's source rotation, exact blank bootstrap, full-frame runtime argument, and inherited source calibration gives the ordinary ZFC consistency calibration for the combined 243 table. The concrete Lean transport remains to be emitted and checked, and the rotation244-to-calibrated-source bridge has not acquired a new kernel proof in this review.

This route does not assume that QT244 and Routing245 have identical intermediate binary tapes, nor that two equivalences from a common ancestor automatically justify arbitrary simultaneous patches. It uses the complete set of local compensation hypotheses, checked against the actual rotated table.

## Bootstrap, runtime, and evidence limits

The new packet reports a 407,931-step blank prefix, 16 later than Routing245, reaching the same complete frame: head −5, marker −6, header 176, span 181, logical registers `(3,0,0,0,3,0,0,0,0)`, 167 spare ones, and 351 one-cells. Its whole-frame theorem quantifies all nine natural registers, an independent nonnegative gap, and every nonempty finite spare suffix. Positive decrement and pointer overflow enlarge the span appropriately; increment appends a value-one spare. These are sufficient inductive frame contracts. The reported expanded census is 8,390 cases and 2,312,438 symbolic rules; 487 of 488 rows are used, with retained `(27,1)` unused. Unused total rows do not invalidate source execution coverage and do not themselves permit deleting state 27.

I reviewed these arguments and their bindings but did not rerun them. The combined 243 bootstrap time is not inferred by adding the two separate timing differences: those differences depend on traversed blocks. It needs its own exact computation if a numerical startup time is to be published. The direct binary fold theorem already transports blank halting without requiring a guessed combined time.

One delivered auxiliary, `code/check_whole_frame_candidate.py`, has an `IndentationError` at line 22. Its main body uses one-space indentation after an inserted four-space assertion guard. This is a reproducibility defect in that auxiliary. The advertised primary `verify_all.py --whole-frame` path calls the separately valid `check_runtime.py --expanded`; it does not invoke the broken auxiliary. All other nine top-level code scripts parse. This review preserves the original file and makes no supplied repair or execution.

The packet's statement that 245's kernel endpoint was still open describes its pinned historical baseline; the currently maintained Routing245 and compensated244 external endpoints are now checked. The new rotation/combined tables are different artifacts and do not inherit those exact endpoint statuses automatically. The ordinary equivalence has no consistency premise. Actual nonhalting follows conditionally on consistency; two-sided independence under bare consistency does not follow. No new all-internal PA comparison or native axiom transport is supplied by this packet.

The other reported grammar searches, source NIP rewrites, and formalism alternatives are separate research, with their own limitations. They are not premises of this 243 combination. Drop's intake review covers their full inventory and manuscript scope; this review focuses the new QT proof and its interaction with the checked compensated fold.
