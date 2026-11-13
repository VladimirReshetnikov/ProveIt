# Review of the AQ16 finite reduction audit

The [review checker](review.py) exited zero and reran the separately written
[AQ16 finite audit](../aq16-independent-audit/README.md), reproducing its
recorded output exactly. The actual review exit is in
[terminal-observation.json](terminal-observation.json), and the
[receipt](receipt.json) binds the compared source and graph hashes. This is
ordinary integer algebra, not a Lean replay or a formal PDF interpretation.

The audited elimination is sound under the stated hypothesis `beta >= 2`:
the deleted residual forces `dValueVariable = DstarComputed` at an AQ17 zero,
and the seven other residuals are preserved after substitution. For positive
surviving witnesses, write `q = 1 + J*beta`, `a = X*Y+Y`, `U = Y*q^2`,
`H = 4*a+3`, `k = eta+zeta`, and `R = rankVariable`. Exact integer algebra
identifies

```
DstarComputed = U*(X+a*eta) + (U*a*Y-H)*k
                + H*(U*gamma+X*Y*q+R+1).
```

Here `q >= 3`, `a >= 2`, and `U*a*Y >= 9*a > H`; each summand is positive.
Consequently a positive child zero reconstructs a positive deleted witness.
The audit uses integer subtraction throughout; treating the subtractions as
truncated natural subtraction would require separate justification.

The beta premise matters to this *uniform positivity argument*. With
`J = X = Y = eta = gamma = R = 1`, `zeta = 33`, all other witnesses 1,
and `beta = 1`, the parent circuit gives `DstarComputed = -2`; changing only
beta to 2 gives 419. This positive assignment is **not claimed to be a zero**,
so it does not disprove a different beta-1 equivalence. The audited actual beta
is the recorded `2^94517 - 1`, which satisfies the required bound.

A separate gate-level degree propagation gives an upper bound of 16 for every
residual and 32 for the output. For the lower bound, the graph has
`M^2 = (1+J*beta)^6 (J*beta)^2` and
`ell = X*Y^2*(eta+zeta)`. In `A0`, the monomial
`J^8 X^2 Y^4 eta^2` comes from `-M^2*ell^2` with coefficient `-beta^8`;
the other `A0` terms cannot supply that witness monomial. It remains nonzero
after the actual beta specialization. A nonzero leading real sum of squares
cannot cancel, so the degree is exactly 32. The review also checks rejection of
a changed binding sign and deliberately rejects optimized Python.

This review found no error in the finite AQ17-to-AQ16 argument. It does not
establish AQ16 Lean transport, an internal iPRA proof, a paired replay, global
minimality, or formal semantics for the PDF. The recorded port-to-PDF link
retains the earlier manually transcribed decoder/rank boundary.

Run with ordinary Python after preserving and moving aside only this packet's
receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/aq16-finite-audit-review/review.py
```
