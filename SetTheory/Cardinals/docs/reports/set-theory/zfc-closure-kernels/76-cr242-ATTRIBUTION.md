# Attribution and scope of this contribution

Prepared on 18 October 2026 for Vladimir Reshetnikov's ProveIt repository.

The inherited numerical calculus, set theory, proof enumerator and machine originate with **Mira-Cult**. The public end-to-end verification is credited to **Jeff Ketchersid**. The compiler framework is credited to **Andrew James Wade**. ProveIt's contributors and incoming research supplied the preceding register permutation, prefix initialization, grammar/routing reduction, compensated fold, QT rotation, machine combination, and proof developments. This package does not reattribute those contributions.

The new contribution is the explicit deletion of inherited state 15 by context-dependent reuse of state 27, the ordinary whole-tape positive-block proof, independently written local checkers, exact candidate/initialization/runtime verification, and accompanying source/acceptance research. The search identifies a concrete optimization opportunity created by the preceding QT rotation. It does not claim that unreachable-branch reuse, abstract interpretation, loop rotation, or stuttering simulation are newly invented general techniques.

`reference/baseline245/` contains the exact 291 files selected by the maintained combined243 reproduction index. Original notices and license files remain in their original locations. `reference/ATTRIBUTION-source71.md` is retained as historical source attribution; its descriptions of the original source71 package are not descriptions of the smaller selected reference subset in this package.

The wrappers `code/verify_runtime.py` and `code/verify_literal.py` adapt the combined243 wrappers to the exact 242-state table, bind its hash, update the state/row census, and require complete row coverage. Their underlying symbolic induction rules are unchanged. The independent local checkers and dense/sparse blank comparison are separate implementations.

The main report distinguishes new ordinary proofs, inherited calibration, symbolic-induction replay, finite regression, and proof-assistant status. No new Lean/Rocq compilation was performed. Existing licenses continue to govern the inherited material; this notice does not replace or override them.
