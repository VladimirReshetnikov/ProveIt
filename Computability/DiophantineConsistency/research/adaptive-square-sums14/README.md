# Fourteen-variable degree-30 square-witness equation

Starting from the proved 13-variable degree-36 square sum, introduce one new
positive coordinate `squareVariable`. Replace `V*V` in its auxiliary residual
by `squareVariable - 1`, and add

```
(squareVariable - 1 - V*V)^2
```

to the sum. The resulting `candidate.json` has 14 positive variables and 91
live unshifted binary operations. `verify_degree.py` checks the five residual
degrees `15, 13, 8, 10, 12`. The first square is the only contribution of
degree 30, and its degree-15 leading polynomial has a nonzero coefficient
`-2*beta^9` at the actual positive fixed beta; thus the output has exact
degree **30**, even after fixing the ports and applying the positive shift.
This is an integer-polynomial certificate, not a Lean theorem about degree or
a minimality claim.

`AdaptiveSquareWitness14` binds its literal to the pinned circuit and to a
one-hole version of the existing 13-variable sum. In every IΣ₁ model it proves
both directions of the shifted zero-existence comparison: a 14-variable zero
projects to a 13-variable zero, and a 13-variable positive zero extends by
choosing the extra coordinate as the square of the signed ordinate's magnitude
plus one. Its `shifted_no_zero_iff` states the resulting universal no-zero
equivalence for arbitrary integer ports. `verify_literal.py` compares the
literal's 14 variable aliases, four ports, and 91 operation rows directly with
`candidate.json`. Both checkers work under normal Python and `python -O`.

The two model/check Lean replays matched on the same historical model provider;
see [the focused replay](../../reviews/adaptive-square-sums14-model-replay/README.md).
Transitive project, package and dynamic ancestry remains inherited. The native
intuitionistic PRA endpoint for this new expression is being assembled and is
not claimed by the model theorem alone.
