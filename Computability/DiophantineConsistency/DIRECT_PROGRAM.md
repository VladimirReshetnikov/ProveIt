# Closed code for the actual refutation test

[`DirectScalarEnumerator.program`](Lean/DiophantineConsistency/DirectScalarEnumerator.lean)
is executable data of type

```lean
ScalarPRCode.Realizes haltingTest
```

It supplies the concrete program input required by
[`ZFCFromProgram`](Lean/DiophantineConsistency/ZFCFromProgram.lean).
Its correctness theorem concerns the exact `haltingTest` already connected
to syntactic ZFC refutation, so no additional simulation premise is needed.

The construction follows the arithmetic semantics of the six-register
enumerator. A state is encoded by five nested applications of `Nat.pair`
to its six registers. An option state uses zero for `none` and the successor
of the state code for `some`. All arithmetic branches, formula constructors,
axiom-stack constructors, fetch operations, and command effects are compiled
directly into supplied scalar programs.

[`DirectScalarArithmetic.lean`](Lean/DiophantineConsistency/DirectScalarArithmetic.lean)
constructs programs and specifications for constants, addition,
multiplication, predecessor, truncated subtraction, equality branching,
and iteration. The enumerator's Cantor pairing is compiled from its
triangular-number recursion. Its inverse follows the source's recursive
walk through antidiagonals. Neither division nor a search operation is
needed.

The final iteration starts at the literal initial state and preserves the
option-state encoding at every step. Testing for encoded zero therefore
agrees exactly with `haltingTest`, including its output encoding.

Every data definition is a computable `def`. No primitive-recursiveness
proof is reified, no existence witness is selected, and no consistency
assumption enters the construction. Lean checks the full evaluation
specification; its transitive axiom audit reports only the standard
`propext`, `Classical.choice`, and `Quot.sound`.

An independent evaluation of `ScalarPRCode.nodeCount` gives **31,889**
nodes for this program and **31,487** after the checked scalar optimizer.
The fixed binary Cantor-pair helper is composed with the pair of its
operand programs, so each operand is computed once at that composition.
Inlining the operands into the triangular formula instead produced
6,928,507 nodes in a temporary comparison; both versions were checked
against the same `haltingTest` specification.
