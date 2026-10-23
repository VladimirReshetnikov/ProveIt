# Direct graph data for the refutation checker

[`DirectGraphEnumerator.program`](Lean/DiophantineConsistency/DirectGraphEnumerator.lean)
has type

```lean
GraphRep (fun v : Fin 1 → ℕ => haltingTest (v 0))
```

It supplies finite representation syntax for the exact bounded test of the
six-register refutation enumerator. Elementary arithmetic is represented
using the checked arithmetic and branching graph constructors. Its
register and option encodings are the same as the closed scalar program.
The raw command effect is connected by the existing
`DirectEnumerator.rawStep_eq` theorem to the literal enumerator semantics.

[`CantorRepresentation.lean`](Lean/DiophantineConsistency/CantorRepresentation.lean)
uses the quadratic identity

```
2*P(a,b) = (a+b)*(a+b+1) + 2*b.
```

The coordinate pairing graph has zero witnesses. Either inverse projection
has one witness, supplying its missing pairing coordinate. Their correctness
uses the checked inverse identities for the source's Cantor pairing.
No triangular-number or inverse-walk recursion is represented by a trace.

Only the outer bounded iteration uses a beta-function trace. Its specialized
certificate retains the initial entry, final entry, and bounded transition
condition. It omits the unused scalar recursion parameter and directly
applies the step graph to the previous trace entry, avoiding a paired step
argument and its inverse projections.

This alternative can feed `GraphRep.existsValue` directly and then the
quartic and Jones compilers. Its evaluation specification has no extra
semantic assumption. All data constructors are computable, and the
transitive axiom audit reports only Lean's three standard axioms. No exact
size comparison of the resulting complete representation is claimed here.

[`NativeZFC.lean`](Lean/DiophantineConsistency/NativeZFC.lean) now closes
this alternative: `noNaturalZero_iff_conZFC` and
`noPositiveZero_iff_conZFC` have no supplied program, representation,
consistency, or compiler hypothesis. `hasZero_iff_explicit` connects its
solvability to the earlier closed scalar-program construction without
assuming consistency.

`NativeZFC` now selects the further source reduction in
[NATIVE_FORMULAS.md](NATIVE_FORMULAS.md). Its one-step graph uses exactly
1,742 witnesses rather than this baseline's 6,924, as proved by Lean
definitions. Polynomial formula blocks, denominator clearing, and retention
of the existing output coordinate account for this reduction. These counts
do not include the final quartic flattening.
