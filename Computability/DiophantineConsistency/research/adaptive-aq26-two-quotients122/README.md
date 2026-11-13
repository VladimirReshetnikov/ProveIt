# Two positive quotients: 26 variables, 122 operations, degree 8

This source-only candidate replaces the two positive root witnesses in the
[26/126/8 positive-variable graph](../adaptive-square-sums26-degree8/) by
their positive quotients. Its positive graph has 26 variables, 122 arithmetic
operations and degree 8. Substituting `1 + n` for each positive variable gives
a 26-variable natural graph with 148 operations and degree 8. The comparison
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

Then exact polynomial identities, checked from all 126 parent rows, show
`parent.A0 = s² * (u² - N0)` and
`parent.A1 = t² * (v² - N1)`. These parentheses are the two child norm
residuals. The other 15 residuals agree exactly, including the two factored
root-binding differences. Both outputs are exactly the sum of the squares of
their 17 residuals. Hence a child zero lifts to a parent zero.

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
all variable bindings, all four ports, all 126 operations and the output of
[`AdaptiveAQ26Literal.literal`](../../Lean/DiophantineConsistency/AdaptiveAQ26Literal.lean).
The source of the existing model quotient lemma and
[`IPRAAQ26Native.literal_equivalence`](../../Lean/DiophantineConsistency/IPRAAQ26Native.lean)
are hash-pinned as well. The parent's native result is a historical author-side
hybrid with a separate standard-theory client; see the parent README and its
[standard client record](../ipra-standard-aq26/README.md) for the precise
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
python3 -I -S -B research/adaptive-aq26-two-quotients122/build.py
python3 -I -S -B research/adaptive-aq26-two-quotients122/check.py
```

The first command regenerates both JSONs from the pinned parent, and the second
checks their pinned hashes, all source rows, topology, liveness, explicit natural
shift, exact sparse-polynomial residual identities, sum-of-squares wiring, and
degree. Degree at most eight follows from the 17 residual degrees. Exact degree
eight follows from the port-independent term `cSquareVariable²*i²` of
coefficient one in the degree-four residual `g72`; a sum of squares of real
homogeneous polynomials cannot vanish identically. These checks are not a
Lean elaboration or a proof of a globally optimal equation. The stored
[`receipt.json`](receipt.json) is the deterministic output of the second
command.
