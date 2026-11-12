CHECKER REFACTORING SUPPLEMENT
=============================

This supplement refactors the existing deterministic auxiliary calculus.
It contributes implementation reductions only. The mathematical theory and
its guarded public-language interpretation are inherited from ProveIt at
commit 8eb71c1e570e07ef45ead686628e77f18ef34798.

Run:

    python3 reproduce.py

The result is evidence/metrics.json and evidence/validation.json, plus
gzip-9 copies of complete normalized program sources. CPython 3.12.14 is
the source-normalization and measurement environment.

Programs:

    code/checker_exact.py          Exact Boolean-dispatch replacement only.
    code/checker_compact.py        Paired comparison and integer/list predicate.
    code/checker_compact_zero.py   Same, with inherited neutral-zero convention.
    code/checker_ast_zero.py       A separate source optimized for AST size.
    code/checker_strict.py         Public-goal and complete input validation.
    code/checker_strict_control.py Matched old-kernel control with same validators.

The strict control is a derivative, not an unchanged frozen source. Exact
upstream files and their MIT No Attribution license are under reference/.
The fixtures in fixtures/local/ are unchanged upstream payloads. The zero
fixtures change only empty-array instruction majors into numeric zero.

Acceptance means successful process exit and exact stdout ACCEPT followed
by newline. Uncaught exceptions reject. Unused prefix data is inert in compact
programs; the strict programs nevertheless validate its integer/list syntax.

ARGUMENT.txt states the contracts and proof details. In particular, the
compact checker is not a validator for every claimed public statement shape,
the entire auxiliary syntax is not claimed bi-interpretable with iPRA, and
the paired comparison does not preserve all malformed JSON acceptance cases.
