# Conditional uniform projection contradiction

`Trace74UniformHeightContradiction.lean` proves two ordered-ring lemmas.
For `h>0`, `Y≥1`, `L≥1`, `K=4L`, and the explicit height bound
`X>8hK²Y²`, the reduced projection product is positive and strictly below
`H=4Y(X+1)-1`. In a discretely ordered ring, the same hypotheses and
divisibility of that product by `H` are contradictory. Discreteness is the
explicit assumption that every positive element is at least one; it is not
assumed for arbitrary ordered rings.

The theorem is conditional. It does not derive the stronger height bound,
discreteness for a specific difference ring, the projection from a graph
zero, the near-diagonal index window, or an iPRA endpoint. An independent
source review checked the factor and height inequalities before the final
divisibility lemma was added; it did not replay Lean or audit that addition.

The bounded Lean 4.32.0 author check used the `LEAN_PATH` provider order in
the [uniform reduction record](../trace74-uniform-projection-reduction-draft/README.md),
with `timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74UniformHeightContradiction.olean`. Tool
session 88935 exited 0; both axiom reports list only `propext`,
`Classical.choice`, and `Quot.sound`. Source SHA-256 is
`11b3dffc4f8849fb5610c382740c0c27f018d2e8e7df84a2295a316ceb4c77ab` and
object SHA-256 is
`c994954d496b9bc17f1354d28342699e2b0e02bd91eac3f0c3333421143c159e`.
The captured provider's direct `Trace74Projection.olean` SHA-256 is
`6465507ef633e37d54e61182779c698d5d2da3aaf5f9c5c8963b62944b19bc77`.
Earlier checks failed on an incompatible broad tactic import and two
elaboration errors. This author check does not authenticate transitive
provider or package ancestry and is not an independent replay.
