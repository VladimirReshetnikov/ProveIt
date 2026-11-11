# Independent review: bounded residual-shear obstruction

**Result: pass for integer-polynomial multipliers.** At the authenticated compact44 port bytes, integer polynomials P, Q and S of total degrees at most 2, 2 and 5 cannot make `A0+P*A1+Q*(Fa−1)+S*g72` have total degree below 15. This says nothing about other circuit transformations, larger multipliers, arbitrary rational coefficients with denominators divisible by the test prime, positive-domain-only identities, or global minimality. No Lean or file-binding theorem was run.

The reviewed first-residual cancellation gives `deg A0≤15`. Independently inspecting the main graph yields `Dstar=U*a*c+W`, `Delta=a²+H`, and `W=U*X+H*shift`, hence

`A1=2*U*a*c*W+W²−U²*(1+H*c²)`.

The source bounds `deg(U,a,c,H,shift,W)≤(3,2,2,2,4,6)` imply `deg A1≤13`. The other two residual bounds are 13 and 10. At the authenticated bytes, a generic finite-field ray attains degrees 15, 13, 13 and 10. On the separate ray with every witness coefficient one except `f=i=u=0` and `gamma=−beta*(beta−1)`, whole-graph evaluation modulo 1,000,000,007 leaves A0 at degree 15 with leading coefficient 142738814, while the other three have degrees at most 12, 12 and 9. Each allowed correction then has degree at most 14 on that ray. Reduction modulo the prime is legitimate for integer coefficients; choosing zero ray coefficients is valid for a polynomial identity even though the original zero problem uses positive witnesses.

The checker reproduces the author and prior 88/30 receipts, reauthenticates all port bytes, confirms the relevant graph wiring, and independently evaluates both rays with sparse polynomial arithmetic. The exact cancellation is a formal identity; no positivity or zero-equivalence claim for a modified graph is needed. Run from `Computability/DiophantineConsistency` with `python3 -I -S -B reviews/ordinary13-88-residual-shear-obstruction-independent/check.py`; stdout must match `result.json`.
