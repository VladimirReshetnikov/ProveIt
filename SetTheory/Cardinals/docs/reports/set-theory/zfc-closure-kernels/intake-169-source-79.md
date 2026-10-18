# Source 79: zero-branch reuse and a native stack frontend

Source 79 is `zfc242-zero-branch-reuse-20261018.zip`, delivered in `d5845120023085f81694ee5b8babb95cd5fa50ef` against `e58338db7545909907e07a7603e8eb88625c527a`. Its 71 members comprise 47 new `79-zb242-` files, 13 existing aliases, three batch aliases and eight archive-only members. Its delivery README is `README.txt`. The standalone stack-kernel research note/README, codecs, exact packets and provenance are retained; the main paper and its included proof sections remain recoverable from the committed ZIP. A nested vendor archive is one preserved data member, not a separate intake or a reason to remove the corresponding older queued archive.

The machine deletes old 15, redirects `11/0` to 27 and changes `27/1` to 22. It is the entire primary-A table after renaming surviving 15 to 27. Its checkpoint proof uses left zero at 18/47/65 and current zero at 27; two old steps match two or four new steps at the exceptional caller. Arbitrary tape context is preserved. The 17/39 fold therefore yields current 241 under the same rename. The separate note about four transfer-plus-one rotations from logical register 6 to logical register 5 (X to H) gives 6,455 source leaves and 202 interned subtrees, with no extra binary deletion.

The genuinely different frontend uses unconditional native stack equations:

```
V(P(x,s),d) = x
V(P(x,s),A(j,d)) = V(s,j)
```

A serves both as selector successor and atomic-class constructor. Finite head/tail equations generate the selectors, and prepending handles de Bruijn binding without conditional indexed-update equality and its explicit congruence completion. A descriptor reserves coordinate 2 for its class code, y at 0, x at 1 and parameters from 3. The code is constructed before its enclosing descriptor, avoiding a circular-code assumption.

The upper model is defined on a countable carrier using disjoint increasing P/A/J/Q codes, terminating selector decoding and structural evaluation. Each fixed descriptor is a finite pure-membership relation with finitely many parameters; the entire external decoder is not thereby an internally definable relation in arbitrary nonstandard arithmetic models. Empty-seed EPSC calibration depends on the earlier Sources 14/08/40. The Boolean conversion keeps native operations and equations on that **same carrier**, equips it with a Boolean algebra, and Booleanizes predicates. In reverse, an ultrafilter acts on predicate values only. The powerset/retraction construction used for an equality-free clause theory cannot simply be substituted when native equations must remain true.

The explicit-Pick packet has **1,169 complete bits, 14 equations, 214 term nodes, 16 symbols, three local variable slots and five-bit opcodes**. The derived-Pick alternative has 1,201 bits, so fewer symbols did not make it smaller. The independent static decoder/encoder reconstructed both delivered bitstrings exactly. The supplied stack builder/checker itself was not run during this comparison.

Two reviewer-derived observations are retained separately from delivered results. Choosing the transported same-carrier Boolean top to equal d permits truth fusion; direct syntax accounting gives 1,166 bits, a three-bit header saving. Directly substituting `E(x,y)=eps(P(x,P(y,d)),A(d,A(d,d)))` instead grows to 1,486 bits, or 1,483 with truth fusion. These are specified syntax-only transformations, not freshly executed complete frontend certificates. A selector dispatch for native stack operations would need its own same-carrier interpretation and full term/arity accounting; Source 77's equality-predicate quotient argument does not already prove it.

The primary executable entry points are `code/prove_zero_reuse242.py`, `code/verify_candidate.py` and the aggregate `code/verify_all.py`; contextual fold searches and `research/stack-kernel/stack_kernel.py` are distinct tasks. Delivered verification/search outputs remain inherited. The [pair review](data/intake169-detour-zero-review.md), [receipt](data/intake169-detour-zero-review.json) and [supplement](data/intake169-secondary-search-supplement.md) preserve these boundaries. The packet is a promising alternate representation, with no complete smaller binary interpreter, new 240-state table, kernel-checked consistency interpretation or internal PA endpoint supplied.
