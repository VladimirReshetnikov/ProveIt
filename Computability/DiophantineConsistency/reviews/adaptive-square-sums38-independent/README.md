# Independent review: 38-variable quartic reduction

The corrected [38-variable candidate](../../research/adaptive-square-sums38-two-quadratic-products/README.md)
and this independent exact checker reproduce. The local algebraic reduction,
positive-domain witness maps, operation accounting and quartic degree have
the stated external mathematical form. This is not a Lean elaboration or an
internal iPRA endpoint for the new graph.

The positive candidate has **38 positive integer inputs**, 160 live binary
operations and 29 squared residuals. Its separate natural candidate replaces
each positive input by a distinct nonnegative input plus one, giving **38
nonnegative inputs and 198 live operations** in that straight-line program.
The checker verifies all inputs, ports and operations are used, checks every
graph dependency and recomputes the two operation counts. These operation
counts include the 38 explicit shift additions in the natural graph; they are
not a claim of global minimum.

The old positive graph has 40 inputs, 166 operations and 31 residual squares.
The child deletes exactly the two named product variables and their two
squared constraints, while substituting

```text
ellProductVariable   = ellVariable * (ellVariable + eta + zeta)
deltaProductVariable = deltaVariable * cSquareVariable.
```

The independent checker reconstructs the actual sum chains and confirms that
every residual square occurs exactly once; in particular, the corrected
`add_scaledIndex` chain includes `add_product2`. Sparse integer-polynomial
comparison with all four ports kept formal establishes that all 29 child
residuals equal the corresponding parent residuals after this lift and both
removed parent residuals become zero.

For a positive child tuple the two inserted products are strictly positive:
all five factors `ellVariable`, `eta`, `zeta`, `deltaVariable`, and
`cSquareVariable` are positive. Thus lifting preserves the positive domain and
maps every child zero to a parent zero, for arbitrary integer port values.
Conversely, a parent zero is a sum of integer squares, so every residual is
zero; its two deleted constraints force those products, and projection gives a
child zero. The lift and projection are inverse on zeros. Translating the
positive graph to nonnegative inputs via `x = n + 1` is a bijection over the
standard natural numbers. These maps must still be formalized for the intended
arithmetic models; this review does not claim that has happened.

Each of the 29 child residuals has degree at most two in the unknowns. The only
residual with a `firstQuotient²` term is the first norm residual, where its
coefficient is one. Consequently the output has `firstQuotient⁴` coefficient
one and exact degree **four**, independently of the four fixed port values.
The positive-to-natural shifts preserve that leading coefficient. A bounded
formal-port scan independently reproduces the reported 23 direct single-
variable substitution results; it is not a proof of global minimality or of
impossibility after different refactoring, simultaneous elimination or fixed-
port specialization.

The parent JSON matches `AdaptiveQM40Context.literal` row for row, and the
parent native and standard endpoint sources explicitly use its `positiveShift`
at `CurrentWindowCarry2011.ports`. Historical author-side endpoint results
retain their documented provider and ancestry limitations. To inherit an iPRA
statement, the new zero maps, positive-variable construction and no-zero
bridge must be proved in the appropriate models and composed with a compatible
checked parent endpoint. The new graph is **not** the compact-port natural-79
graph, and these external algebraic identities alone do not establish the
new iPRA derivation or physical PDF binding.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-square-sums38-two-quadratic-products/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-square-sums38-two-quadratic-products/result.json
python3 -I -S -B Computability/DiophantineConsistency/reviews/adaptive-square-sums38-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/adaptive-square-sums38-independent/result.json
```
