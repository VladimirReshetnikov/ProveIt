/-!
# Cubic bisection example: implementation outline

Target: a fixed rational-code presentation and a PCFM trace proving the
bracketing invariant for `F(y) = y^3 + y - q`.

Steps:
1. import the future rational presentation;
2. define the state `(L,U)` using `pairT`;
3. define exact rational midpoint and the reflected comparison `F(M) <= 0`;
4. define the frozen branch step as a `PTm` and compile it with `recDef`;
5. prove the QF invariant:
     L < U /\ F(L) <= 0 /\ 0 <= F(U) /\
     2^t * (U-L) = U0-L0;
6. invoke `Framework.Trace`;
7. prove strict monotonicity from
     (v^3+v)-(u^3+u) = (v-u)(v^2+u*v+u^2+1);
8. export an interval of width at most `2^-k`.

This example is intentionally not presented as checked by the artifact.
-/
