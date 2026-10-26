# A quartic compiler that preserves circuit sharing

[`DAGQuartic.lean`](Lean/DiophantineConsistency/DAGQuartic.lean) supplies a
generic alternative to expanding a shared circuit into a large expression
tree before introducing gate variables. It accepts any literal topological
`ArithmeticDAG` program, including subtraction and arbitrary signed integer
constants. The original inputs are natural numbers; intermediate values may
be negative.

For a circuit with `n` inputs and `m` stored nodes, introduce two natural
variables `u_i,v_i` per node and write `z_i=u_i-v_i`. The polynomial is

```
z_output^2 + sum_i (z_i - rhs_i)^2 = 0,
```

where `rhs_i` is the literal constant, input, fixed coefficient, or binary
operation at node `i`. References to an earlier node read its two variables.
Each computation is stored once, even if many later nodes use it.
Intermediate registers are witnesses of this new quartic, and are charged
in its variable count; they are not free variables hidden in the ledger.

Lean proves all of the following for the actual executable syntax and its
ordinary integer multivariate polynomial:

* Exactly `n+2*m` natural variable slots, including both parts of every
  stored value. This simple first compiler also charges leaf nodes.
* Total degree at most four.
* At most `12*m+4` binary operations in the entire syntax tree. The bound
  charges every repeated signed-variable read, square and sum operation.
* For each natural input tuple, gate witnesses exist exactly when the
  original circuit's integer output is zero.
* Existentially closing the original inputs gives the same solvability
  equivalence for the ordinary polynomial.

The proof uses that a sum of integer squares vanishes exactly when every
residual vanishes. Strict topology then makes a table satisfying the local
node equations equal to the circuit evaluator. In the other direction the
explicit witnesses are `max(value,0)` and `max(-value,0)`, implemented by
`Int.toNat`. No choice, natural-valued-intermediate hypothesis, or sampling
argument supplies the data.

The dedicated checks include a shared negative intermediate in
`(x-3)^2-1`, successful and unsuccessful inputs, and rejection of a self-edge.
The generic theorems' axiom audits use only Lean's standard axioms.

This is a reusable arithmetic compiler, not yet a compiled ZFC checker or
a demonstrated size improvement over the closed consistency equations.
A finite proof checker still needs an arithmetic representation of formula
syntax, rule checking and its whole bounded trace. A proof provable inside
ZFC also needs that representation's correctness over internal natural
numbers. Neither obligation follows just from this gate compiler.
