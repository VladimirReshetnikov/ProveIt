# Bounded lexical proof-marker inventory for the nine-source selection

This read-only source inventory scans the **1,354 selected local source
files** in the pinned nine-alternative fixed-85 JSON plan. Every selected
file's SHA-256 is rechecked before scanning. It does not scan the 93
external/frontier modules or their transitive dependencies, inspect any
compiled object, execute Lean, produce `#print axioms` output, authenticate
provider selection, or establish an iPRA proof.

The scanner removes `--` line comments, nested `/- ... -/` comments, ordinary
quoted strings and common character literals before looking for standalone
code tokens `sorry`, `admit`, `axiom`, `unsafe`, `sorryAx`, `native_decide`,
`run_tac`, `implemented_by`, `opaque`, `partial`, `postulate` and
`ofReduceBool`. It also looks for line-start `constant` declarations and
qualified `Classical.choice` occurrences. Synthetic controls exercise nested
comments and strings. Exact file/line/column hits are in `inventory.json`.

For this snapshot the scanner reports **no code occurrences of the listed
escape/declaration tokens and no line-start `constant` declarations**. It
also finds 159 lexical `Classical.choice` occurrences in 51 selected modules.
These are reported separately: classical choice is a Lean foundational
principle, not automatically a proof escape or a claim about which axioms
the final theorem uses. The 94 `axiom` and two `admit` marker occurrences
removed as comments are not counted as source-code declarations or tactics.
Other comment marker counts and all qualified-choice locations are recorded
in the receipt and inventory.

This is **not** a Lean parser or semantic proof audit. It does not interpret
macro/notation or quotation semantics, resolve aliases, examine tactic
execution, reconstruct theorem dependencies, or detect every possible way to
introduce assumptions or unsafe generated terms. It blanks interpolated and
raw string syntax rather than parsing embedded syntax; no `s!"`-style
interpolated string or `r#"`-style raw-string prefix was observed by this
specific lexical counter, which is not a complete Lean syntax check. It does
not determine whether code tokens in syntax quotations execute as tactics.
External and transitive package sources and all source/object collisions are
outside scope. Absence of these lexical tokens is not evidence that the
unelaborated endpoint compiles, has no hidden assumptions, or has a given
axiom footprint.

From `Computability/DiophantineConsistency`, reproduce the read-only scan:

```
python3 -I -S -B research/ordinary13-fixed85-proof-escape-inventory/scan.py | cmp - research/ordinary13-fixed85-proof-escape-inventory/receipt.json
```

The optional `--write` regenerates only this packet's inventory file; it does
not modify selected sources or providers.
