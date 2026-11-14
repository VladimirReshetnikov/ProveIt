# PA194 model-uniform term closing equations

`PA194TermRecursion.lean` constructs one explicit PR `closeCode : Code 3`
from two certified unary pairing projections. Its inputs are a numeric term
code, closing label, and binder depth. It uses the parameter-preserving
course-of-values history to compute earlier function arguments, rather than
requiring an externally fixed depth bound.

For every candidate-PRA model, the theorems `modelCloseBound`,
`modelCloseFree`, `modelCloseNullary`, `modelCloseUnary`, and
`modelCloseBinary` prove the exact numeric constructor equations. All term
fields and both closing parameters may be nonstandard model values. The unary
and binary equations cover the canonical one- and two-element argument-vector
encodings; the nullary equation uses the empty vector. These results require
candidate-PRA certificates for the two pairing projections, whose existential
availability is proved in `PA194StackCode`. They do not assume IΣ₁.

This establishes the numeric recursion equations, not the entire correctness
of Foundation's internal capture-avoiding rewriting on arbitrary model-valued
well-formed syntax. In particular, identifying `closeCode` with Foundation's
`closeLabel` semantics or its typed quotation is still open; so are formula
traversal and the machine/PA consistency reductions. Behavior on malformed
nodes and function arities outside 0, 1, and 2 is not a correctness claim.
See [TERM-HISTORY.md](TERM-HISTORY.md) for the child bounds and history
lookup, and [CLOSE-BOUNDED.md](CLOSE-BOUNDED.md) for an independent
externally finite-shape result.

Run from the repository root with the audited overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-term-recursion.sh
```
