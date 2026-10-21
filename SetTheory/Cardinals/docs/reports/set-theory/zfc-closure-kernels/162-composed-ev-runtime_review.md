# Independent review of the final K215 runtime argument

## Conclusion

The final native table with SHA-256 `03739f080d023166773bc14e7e3a4d8157f81d44c28cd30fef46066b37cf3748` has a coherent, universally quantified primitive-simulation argument. I found no uncovered runtime or source-address obligation in the reviewed code and final receipts. The proof is ordinary mathematical verification by a small executable induction procedure. It is not a newly kernel-checked Lean/Rocq proof. The foundational numerical-calculus calibration is an inherited, separate dependency and was not re-proved by this runtime review.

The accompanying `review_runtime215.py` independently checks the exact receipt/code bindings, all source/guard cases, positive-duration metadata, transition-row coverage, and the interface between binary addresses and ordinal source control. Its output is `runtime-review215.json`. It does not replay the complete symbolic calculations; the packet's full runtime command does that.

## Why the finite construction cap does not bound the theorem

The symbolic state has a literal state label, a head orientation, and the entire tape represented as finite concatenations of affine unary runs, an arbitrary finite spare-list variable, and infinite zero exteriors. The nine primary values, additional gap, and first spare value are independent natural variables. A decrement guard substitutes either zero or `1+n`. The remaining spare list is arbitrary, including empty, so together with the first spare this covers every nonempty finite spare list.

Every successful symbolic rule has a universally quantified justification:

1. A literal step uses an actual table row and a current bit whose presence is guaranteed. An affine run can be consumed literally only when its constant term is at least one.
2. A unary acceleration applies only to a state-preserving row moving in the current scan direction. Induction on the natural run length gives exactly the stated run rewrite, duration, and displacement, including the length-zero case.
3. A list acceleration uses one of four one-block lemmas freshly derived from the exact table. The block proof has arbitrary opaque contexts on both sides, never accesses those contexts, and proves duration and displacement `v+2`. Induction on a finite list gives the arbitrary-list traversal. The normalizer's identity `C(S)1=1B(S)` follows from the empty case and `C(v)1=1B(v)`; its reversal is equally valid.

Each accepted nonhalting case ends by exact equality of the symbolic target tape, state, and orientation, with the calculated head motion also checked. A halting case instead ends at the actual distinguished halt state. Unknown or insufficiently justified behavior raises an error. Exhausting the 4,000-iteration construction cap gives failure, never success. Thus this cap restricts which proofs the procedure can construct; it does not bound register values, gap, spare count, concrete duration, or the subsequent source run. In the delivered receipt, the largest successful construction takes only 460 symbolic rules.

The infinity symbols denote zero exterior tape, not an accelerated infinite computation. Reading the exterior introduces a single zero cell; no rule executes an infinite ray as one finite step.

## Complete coverage and the source-address interface

The reviewed source has 4,751 primitive occurrences, including 1,425 decrement occurrences and one halt occurrence. The 6,176 case summaries have exactly the ordered `(site ordinal, guard)` inventory required by that source: no omitted, duplicated, or extra case. Their symbolic-rule counts total 1,698,790, comprising 1,443,432 literal, 251,558 unary, and 3,800 list rules. Together with the freshly derived block schemas their row inventory covers all 430 native transition rows.

The independent interface audit additionally checks all 6,175 nonhalting guarded successors by two methods: binary increment/truncation followed by zero-padded tree dispatch, and source-tree interval/ancestor semantics. They agree in every case, including both address-overflow cases. After resolution, all bits beyond the target leaf are zero. Consequently a raw successor word and its next primitive address describe the same tape, not merely the same abstract ordinal. An empty control area resolves to source ordinal zero. This closes the small interface that otherwise sits between the runtime checker and the ordinal source-bisimulation checker.

The native-to-legacy mapping used by the symbolic engine is injective, sends native start/dispatcher/halt `0/84/254` to legacy `95/96/254`, and correctly includes the newly used high labels. Native-to-canonical isomorphism and exact blank initialization are independently checked by `audit_table_and_blank.py`.

## Primitive progress and whole-program equivalence

Every duration is a 13-component affine form with nonnegative integer coefficients and a strictly positive constant. The minimum constant over all cases is six, for CH; the minimum over nonhalting cases is 28. For any concrete finite source frame, substituting its natural data and finite spare width yields a finite positive duration.

The target contracts preserve the complete frame invariant: at least one finite spare remains, increment may append a spare of value one, the gap stays natural, and the whole exterior stays zero. Therefore the contracts can be iterated. A nonhalting primitive cannot unexpectedly halt: the symbolic construction would then encounter the absent halt row before reaching its required nonhalting endpoint and reject. It cannot diverge internally because its completed derivation supplies a finite concrete run for every instantiation. It is unnecessary that the selected endpoint be the first clean redispatch; a finite deterministic block between the required boundaries suffices.

Concatenation now preserves halting in both directions. Every finite source execution has a finite machine realization. An infinite source execution contains infinitely many blocks of positive duration, so its machine realization cannot end after finitely many steps. This positivity check is the relevant progress condition; a finite test suite on small natural values would not establish it.

## Ordinary ZFC formalizability and remaining trust boundary

These arguments use finite table calculations, induction over naturals, finite lists and source steps, and exact integer/word arithmetic. They can be formalized in ZFC. The all-case calculations are finite and reproducible; their soundness is supplied by the reviewed induction rules. The separate blank prefix reaches a safe source frame, and the separate source/calculus proof identifies source halting with a finite ZFC contradiction proof.

The evidence does not presently include a formal proof-assistant derivation of the soundness of the Python implementation or a kernel replay of the final table theorem. Ordinary mathematical confidence therefore rests on the rule-soundness argument, correct execution of the pinned checker, and the inherited calibration, rather than on receipt labels alone. The report already makes this distinction explicit. No extra consistency or arithmetic-soundness assumption is needed for the equivalence itself.
