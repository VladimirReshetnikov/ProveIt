# Why the unit residual is still squared

One possible 76-operation probe drops the square from the 77 graph's output,
changing

```
(A1*Na - 1)^2 + M^2 + W^2 + Lt^2
```

to

```
(A1*Na - 1) + M^2 + W^2 + Lt^2.
```

The second expression can vanish by cancellation even when the unit
residual is nonzero. For a concrete assignment in the ordinary integers,
take `A1=1`, `Na=-1`, `M=1`, `W=1`, and `Lt=0`. The unsquared expression
is `-2 + 1 + 1 = 0`, while `A1*Na=-1`, so the squared expression is 6.
The assignment even satisfies `A1≠−1` and `Lt=0`; those two conditions
alone do not eliminate cancellation.

This is a counterexample to the *unrestricted residual-level implication*,
not a solution of the actual graph. The residuals there share the same
positive tuple and fixed ports and satisfy additional polynomial relations.
No claim is made that this assignment, or any other cancellation assignment,
can occur at an actual graph zero. Establishing or refuting zero-existence
equivalence for the proposed unsquared graph remains open.
