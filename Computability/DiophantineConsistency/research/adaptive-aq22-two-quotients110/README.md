# Two positive quotients: 22 variables, 110 operations, degree 10

This source-only candidate replaces the two positive root witnesses in the
[22/114/10 positive-variable graph](../adaptive-square-sums22-degree10/) by
their positive quotients. Its positive graph has 22 variables, 110 arithmetic
operations and degree 10. Substituting `1 + n` for each positive variable gives
a 22-variable natural graph with 132 operations and degree 10. The comparison
with the parent is a reduction in operation count; no global minimum is claimed.
The two graphs are different polynomials: the result below concerns their zero
sets, not equality away from zero.

## Zero-set argument and assumptions

Write `s = scaleVariable`, `t = mainScaleVariable`, `u = firstQuotient`, and
`v = mainQuotient`. For a child valuation, lift the two replaced coordinates
to the parent by `zValueVariable = s*u` and `dValueVariable = t*v`; keep every
other coordinate. This map preserves positivity. Let

```
N0 = 1 + ellVariable * (ellVariable + eta + zeta)
N1 = 1 + deltaVariable * cSquareVariable
```

Then exact polynomial identities, checked from all 114 parent rows, show
`parent.A0 = s² * (u² - N0)` and
`parent.A1 = t² * (v² - N1)`. These parentheses are the two child norm
residuals. The other 11 residuals agree exactly, including the two factored
root-binding differences. Both outputs are exactly the sum of the squares of
their 13 residuals. Hence a child zero lifts to a parent zero.

Conversely, take any positive parent zero in a model `V` of IΣ₁ with the
ordered-ring structure used by the Lean arithmetic library. Vanishing of the
sum of squares gives `z² = s²*N0` and `d² = t²*N1`. All variables occurring in
`N0` and `N1` are model naturals, so these norms are model naturals. The existing
[`ArithmeticAdaptiveQuotients2011.scaled_quotient`](../../Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean)
applies separately to each identity, since `s,t > 0`, producing model elements
`u,v` with `z=s*u`, `u²=N0`, `d=t*v`, `v²=N1`. Since the parent roots `z,d`
are positive, both quotient witnesses are positive too. The two exact
identities and equality of the other residuals imply a child zero. The two
quotients are obtained simultaneously from the same original valuation;
neither step depends on a quotient choice for the other. The same elementary
argument applies over the standard natural numbers. All four fixed-port values
may be arbitrary signed values for these **local** identities and maps: the
norms and positivity argument use only the positive witness variables.

For the natural graph, positive witnesses and natural witnesses correspond by
`x = n + 1`, using existence of a predecessor for every positive model natural.
As usual, the graph's subtractions are evaluated in the associated signed
integer/difference ring. The sum-of-squares zero argument uses its order and
has no cancellation between nonnegative squares.

## Source provenance and limits

[`check.py`](check.py) checks that the pinned parent JSON exactly transcribes
all variable bindings, all four ports, all 114 operations and the output of
[`AdaptiveAQ22Literal.literal`](../../Lean/DiophantineConsistency/AdaptiveAQ22Literal.lean).
The source of the existing model quotient lemma and
[`IPRAAQ22Native.literal_equivalence`](../../Lean/DiophantineConsistency/IPRAAQ22Native.lean)
are hash-pinned as well. The parent's native result is a historical paired replay and separate standard-theory client; see the parent README and its
[historical paired result](../../reviews/ipra-aq22-historical-pair-terminal/README.md) for the precise
provenance and the distinction between the translated selected Foundation
sentence and an untranslated classical sentence.

**No Lean source for this new expression or its model transfer has been
elaborated here.** The mathematical zero-map argument and finite checker do
not by themselves establish an iPRA derivability theorem for the new graph,
nor do they upgrade the parent's provenance. The cited parent endpoint is for
the positive-shifted parent expression, not this new expression.

## Reproduction

Run from the repository's `Computability/DiophantineConsistency` directory:

```
python3 -I -S -B research/adaptive-aq22-two-quotients110/build.py
python3 -I -S -B research/adaptive-aq22-two-quotients110/check.py
```

The first command regenerates both JSONs from the pinned parent, and the second
checks their pinned hashes, all source rows, topology, liveness, explicit natural
shift, exact sparse-polynomial residual identities, sum-of-squares wiring, and
degree. Degree at most ten follows from the 13 residual degrees. Exact degree
ten follows from the port-independent term `deltaVariable*f²*y²` of
coefficient minus one in the degree-five residual `auxResidual`; a sum of squares of real
homogeneous polynomials cannot vanish identically. These checks are not a
Lean elaboration or a proof of a globally optimal equation. The stored
[`receipt.json`](receipt.json) is the deterministic output of the second
command.
