# Polynomial formula blocks in the native refutation graph

[`NativeFormulaSyntax.lean`](Lean/DiophantineConsistency/NativeFormulaSyntax.lean)
supplies literal natural-polynomial syntax for the code constructors,
all enumerated axiom rows, and the gated bundle body. Its basic identity is

```
wim(a,b) = 2*(a+b)*(a+b+1) + 4*b.
```

The evaluation lemmas identify this syntax with the exact existing source
functions, including `bundle222`.

[`NativeFormulaGraphs.lean`](Lean/DiophantineConsistency/NativeFormulaGraphs.lean)
uses the direct polynomial graph constructor to represent each formula
coordinate graph with zero extra witnesses. The entire `axStack` has a
fixed-denominator natural polynomial, supplied by nested applications of
`ScaledNatural.cantorPair`. Clearing that positive constant denominator in
one graph equation also gives zero extra witnesses for the stack coordinate
graph. The gated coordinate graph uses one disequality slack for
`(c-a)*(c-b) != 0`: its zero branch returns zero, and its nonzero branch
returns the polynomial bundle. This saves thirteen witnesses against the
earlier two-equality construction.

The external operand graphs are substituted once into fixed coordinate
blocks. Checked witness-count formulas are:

```
implication arguments: 2 + sum of the two argument witness counts
gated arguments:       4 + sum of the three argument witness counts
stack arguments:       7 + sum of the seven argument witness counts
```

[`NativeGraphEnumerator.lean`](Lean/DiophantineConsistency/NativeGraphEnumerator.lean)
uses those blocks in the source arithmetic checker. Its `program` represents
the exact `haltingTest` graph and retains the single outer beta-function
trace from the earlier direct graph construction. Its local finite
compositions retain the exposed graph output, avoiding an unnecessary
output-value witness. Local equality branches also use the one-slack
disequality graph and retain the exposed output. Their cost is five plus
the four argument witness counts, saving two against the earlier branch.
The full source step has **1,742** witnesses, down from the checked
1,811-witness checkpoint and
compared with **6,924** for `DirectGraphEnumerator`.
Both counts are theorems proved by definitional reduction.

These counts concern the arithmetic graph before quartic flattening.
Clearing denominators and replacing intermediate values by polynomial
syntax changes expression size and coefficients; the source witness count
alone does not give an exact count for the final quartic or Jones equation.
The implementation makes no unmeasured final-size claim.

All data definitions are computable. The row syntax's evaluation audit uses
only `propext`; the stack graph audit uses `propext` and `Quot.sound`.
The complete native refutation graph's audit uses Lean's three standard
axioms and introduces no new assumption or proof placeholder.
