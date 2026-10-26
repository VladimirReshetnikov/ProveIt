# One natural variable per shared arithmetic node

[`NaturalDAGQuartic.lean`](Lean/DiophantineConsistency/NaturalDAGQuartic.lean)
improves the generic shared-gate construction when the source computation
uses natural inputs, nonnegative integer constants, addition and
multiplication. It compares two output wires, so it represents a general
natural-polynomial equality rather than just testing a nonnegative output
against zero.

For `n` original inputs and `m` stored nodes, its actual executable polynomial
is

```
(z_left-z_right)^2 + sum_i (z_i-rhs_i)^2 = 0.
```

Lean proves the source restrictions imply every evaluated node is
nonnegative. Each node therefore needs one natural witness instead of the
two parts used by the signed compiler. Topology and the local equations
make any satisfying witness table equal the actual evaluation table.
Conversely, the evaluation supplies all witnesses explicitly.

The checked counts and semantics are:

* Exactly `n+m` natural variable slots, including every stored leaf node.
* Total degree at most four.
* At most `6*m+4` binary operations in the complete syntax tree.
* For every natural input, gate witnesses exist exactly when the two
  original outputs agree. Existential closure gives the corresponding
  ordinary-polynomial solvability equivalence.

Earlier node computations are reused through their witness variables. All
residual, squaring and sum operations are charged. A checked example uses
the shared circuit `(x+1)^2=9`: five stored nodes, six natural variables,
and exactly 28 tree operations. Checks include both an accepting and a
rejecting input and reject negative literals or subtraction in the source.
All eight axiom audits contain only Lean's standard axioms.

This compiler is an additional size tradeoff for the direct-certificate
route. It does not yet supply its complete arithmetic checking circuit.
The general [signed compiler](DAG_QUARTIC.md) remains available for programs
with negative intermediate values. Neither generic bound measures the
eventual whole ZFC proof checker, nor supplies its internal ZFC correctness
derivation.
