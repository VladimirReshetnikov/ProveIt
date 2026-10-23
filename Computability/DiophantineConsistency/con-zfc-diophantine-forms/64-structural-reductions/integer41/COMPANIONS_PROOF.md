# Exact sextic and octic companions of the 41-integer quartic

The new 41-variable quadratic system admits ordinary polynomial register
elimination. These companion reductions do not introduce any further Pell,
sign, consistency, or compiler hypotheses. They are exact bijections of
zero sets over unrestricted integers, by forgetting and uniquely restoring
polynomially defined coordinates.

## The 36-integer sextic

In `quartic41.json` remove five definition rows and substitute everywhere

    N=q(L+1), X=4 w_scale q, C2=c^2, F2=f^2, Baux=I^2,
    q=beta J+1.

Their five coordinates disappear, leaving 36 integers and 21 residual
equations. Every remaining residual has degree at most three. The source
rows being deleted are exactly their unit-coefficient definition equations;
each vanishes identically after substitution. Thus every new zero restores
one and only one old tuple, and every old zero projects to a new zero.

Let Q36 be the sum of squares of the new residuals in `sextic36.json`.
Its exact degree is six, certified by

    [I^4 g^2] Q36 = 1.

Indeed the retained auxiliary row is `-I^2 g+y^2-1`; squaring yields that
monomial. The exact sparse expansion in the checker confirms its coefficient
and the degree bound on every other term, with all coefficient ports kept
symbolic. Therefore its integer unsolvability is ZFC-provably equivalent
to Con(ZFC) by PROOF41.

## The 31-integer octic

Instead remove the following ten coordinates and their definition rows:

    L=q^2-1, N=q^3, X=4 w_scale q,
    C2=c^2, F2=f^2, Baux=I^2,
    g=y^2-V^2, P=E(c-eta)+eta+zeta,
    D=4 w_scale q+ac+gamma(4a+3),
    Delta=a^2+4a+3.

All right-hand sides involve only retained variables. There are now 31
integer unknowns and 16 residual equations, each of degree at most four.
The source N row vanishes because the simultaneous substitution
L=q^2-1 makes q(L+1)=q^3. Every other deleted row vanishes by its literal
displayed definition. Again, forgetting and restoring these ten coordinates
are inverse maps between the integer zero sets.

The sum of squares Q31 specified in `octic31.json` has exact degree eight,
with the uniform fixed-coefficient certificate

    [I^4 V^4] Q31 = 1.

This monomial comes from the auxiliary residual
`I^2(V^2-y^2)+y^2-1`. The auditor expands the full sum with symbolic ports
and verifies the exact coefficient and upper degree bound. Its integer
unsolvability is therefore ZFC-provably equivalent to Con(ZFC).

## Reproduction

After generating quartic41, run `python3 build_companions.py` (also works
with `-O`). It verifies every eliminated row is the zero polynomial,
emits both complete lists of residuals and variable lists, checks that all
retained variables are live, and certifies both exact degrees and their
unit leading coefficients. Every coefficient is bound to precisely the
same supplied native tuple as quartic41. Named intermediate definitions
inside this proof introduce no extra quantified variables in the emitted
equations.
