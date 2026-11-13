# Decimal display of the ten-positive trace75 candidate

[`equation.pdf`](equation.pdf) and [`equation.tex`](equation.tex) display the
75-operation degree-402 candidate with the directly indexed BFS coefficient
tuple. Its ten strictly positive unknowns have the distinct names `a` through
`j`; the numbered `r` symbols are intermediate abbreviations, not additional
unknowns. The 75 count covers the positive-coordinate evaluator and excludes
the separate positive shifts and construction of fixed constants. The fixed
selector values are printed as decimal integers; the formulas use ordinary
integer arithmetic and powers.

`generate.py` builds the display from the pinned 75-row JSON and reconstructs
all four fixed integers against the complete retained coefficient payloads.
The observed generation in tool session 23536 exited 0; its finite receipt is
[`observations/generation.json`](observations/generation.json). The independent
checker `check_display.py` parses the rendered PDF text, checks all 75 rows,
943 decimal selectors, 41 slots, fixed coefficient formulas and payloads,
and checks word bounding boxes; [`observations/display.json`](observations/display.json)
records its successful rerun. These are external finite checks. They do not
formalize TeX, PDF, or the JSON-to-Lean-file correspondence in Lean.

The separate `check_lean_graph.py` parses the restricted arithmetic fragment
of the pinned Lean `regs` and `value75` definitions and compares their output
with the JSON circuit after exact associative/commutative ring normalization.
It uses interned structural terms rather than random evaluations; its
[`observations/lean-graph.json`](observations/lean-graph.json) records PASS.
This connects the JSON and Lean source through a finite external parser, not a
Lean theorem about source-file or PDF bytes. An [independent audit](../../reviews/trace75-lean-json-structural-independent/README.md)
reproduced the result and checked five rejected parser mutations. The
normalization is sound for commutative rings but is not a complete equality
procedure; it compares the final output rather than each field independently.

`check_liveness.py` finds all 75 rows and all 14 inputs live (44
multiplications, 17 additions and 14 subtractions). `verify_degree.py` obtains
a degree upper bound of 402 from the row graph and a nonzero coefficient of
`t^402` after sending all ten unknowns to `t` modulo 1,000,000,007, proving
exact total degree 402 for the pinned fixed integers. Their finite outputs are
in `observations/`. Neither result is a Lean degree theorem.

A second generation (tool session 71517, exit 0) reproduced the TeX and PDF
byte-for-byte. The [independent display audit](../../reviews/trace75-bfs-decimal-display-independent/README.md)
rechecks the printed rows, coefficients, liveness, and full modular ray
polynomial; it does not replay Lean.

The fixed-port iPRA proof-existence clients for the corresponding Lean graph
have since passed the [compatible-provider final assembly](../trace75-bfs-ipra-final-assembly-plan/RUNNER.md)
and its independent result audit. The four retained baseline objects also have
a [direct-producer audit](../trace75-baseline-four-provenance/README.md); their
upstream and other historical and outside ancestry remain inherited. This
standalone display's connection to
those Lean statements is through the external checks above, not a Lean theorem
about file semantics. It does not replace the maintained root `equation.tex`
and `equation.pdf`.
