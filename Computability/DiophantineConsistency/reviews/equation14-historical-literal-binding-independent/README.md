# Independent finite 14-variable binding review

The guarded rerun of the [historical literal binding packet](../equation14-historical-literal-binding/README.md)
passed in tool session `48043` with observed exit 0. The [receipt](receipt.json)
pins the exact review script, both guarded original scripts and all listed
inputs before and after the run, including both versions of every source in
the 24-module declared closure, the dependency parsers, Lean probe and fixed
coefficient files. The normal reruns reproduced both earlier
receipt contents byte-for-byte: they check 14 coordinate bindings, four
symbolic ports, 22 arithmetic definitions, final product wiring and three
source mutations against the TeX-checked 65-gate graph. They also check the
declared 24-module source closure, isolate the historical/current
`NaturalExpression` difference to one theorem proof, and rebuild the current
PDF byte-for-byte from the pinned TeX.

Both original scripts use Python assertions. They now explicitly reject `-O`
and `-OO`; all four optimized-mode negative controls passed. Their original
saved receipts predate the guard, and the original version remains available
in commit `6b6f1911c7`. The independent script likewise refuses optimized
Python and must be run in normal mode.

The review independently reran the bounded Lean `#eval` probe in a new
temporary directory using the audited fresh author provider, with toolchain,
source and inputs pinned. It checked the actual subprocess exit 0 and full
decimal outputs for all four ports against both the saved outputs and the
entire decompressed graph coefficients. It also reran the finite printed
recipe reconstruction, including 942 tiles and 885,481 rank comparisons.
Its output matches the earlier reconstruction after excluding the explicitly
identified unrelated `equation86.tex` hash field.

This does not turn the PDF into a formal Lean statement: the fixed decoder,
tile-table, rank and port recipes remain manually transcribed in the existing
finite checker, which pins the displayed TeX block rather than generally
parsing those recipes. The Lean `#eval` is computation followed by an external
integer comparison, not an internal Lean equality theorem. This review is not
an independent Lean endpoint replay and does not authenticate package-
transitive or dynamic-loading ancestry. It retains the historical-source,
single-author and unobserved Foundation wrapper-exit limitations.
