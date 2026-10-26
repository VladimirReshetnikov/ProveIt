# Independent arithmetic review of the five-coordinate growth block

Reviewed against the inherited `growth_proof.md` from incoming
`ConZFC_Pell_Growth_210_2026-10-25` and the root agent's proposed replacement.
This is an ordinary mathematical review, not a new proof-assistant build.

## Proposed block

Use the cofinal horizon t=64+4z^2 and five new integer coordinates
S,T,Z,X,u. Retain the source's existing F coordinate and impose

    S=t^2,
    T=S^2,
    Z=T*F,
    X^2-Z^2-2*Z*F=1,
    F=T*(2*u+1).

Every residual is quadratic. These rows imply T=t^4>0 and

    X^2-((T+1)^2-1)*F^2=1.

The odd factor is nonzero, so F is nonzero and even. Pell classification
at a=T+1 gives |F|=Y_n(a) for some n>=1. Since Y_n(a)=n modulo a-1=T,
the divisibility T|F implies T|n, so n>=T. Thus

    |F| >= (2*T+1)^(n-1) > (2*t^4)^(t^4-1).

The displayed strict inequality is valid because T>=64^4>1. It implies
the old source's required sign-free growth scale, as shown next.

## Comparison with the actual source majorant

Let d=2^19 and L=8^(d-1)*t^d. The constructor-depth proof supplies
this L independently of the growth block. For t>=64,

    t^3>=2^18=d/2,
    t^4-1>t*(d/2-1).

Also

    (2*t^4)^(d/2-1) / L
       = t^(d-4) / 2^((5*d/2)-2) > 1.

Indeed t>=64 gives t^(d-4)>=2^(6*d-24), and
6*d-24>(5*d/2)-2 for the fixed d. Consequently

    |F| > (2*t^4)^(t^4-1) > L^t >= t^t > t.

This comparison uses integer powers and inequalities only. In particular,
the delayed sign bootstrap from the old proof remains valid once its
other interfaces have been checked: |F|>t, F even, and F nonzero are
available without assuming F positive.

## Cofinal completeness and binomial parity

For a given finite refutation, choose z divisible by 2^12 and sufficiently
large. Then t is cofinal and

    t=64 modulo 2^26, v_2(t)=6,
    T=t^4, v_2(T)=24.

In particular bit 24 of t is zero. Set a=T+1, n0=T,
y0=Y_T(a), a0=X_T(a). The congruence Y_T(a)=T modulo T shows T|y0.
For odd a the standard Pell valuation identity gives
v_2(y0)=v_2(T)=24, hence b0=y0/T is an odd integer. Since T is even,
the duplication formula gives a0=1 modulo 4.

Choose ell>26 with t<2^ell. Both T/2^24 and b0 are odd. The inherited
normalized Pell permutation theorem at center a0 supplies an odd s,
cofinally in its residue class, satisfying

    (T/2^24)*b0*Y_s(a0)=1 modulo 2^(ell-24).

Take

    F=y0*Y_s(a0)=Y_(T*s)(a),
    X=X_(T*s)(a),
    S=t^2, Z=T*F, u=(F/T-1)/2.

The quotient F/T=b0*Y_s(a0) is odd, and all five rows hold. Moreover
F is positive and

    F=2^24 modulo 2^ell.

Below bit ell, F has exactly bit 24 set, while bit 24 of t is zero.
Above or at ell, t has no set bits. Thus F and t have disjoint binary
supports and binom(F+t,t) is odd. This is exactly the parity condition
used by the later CRT representative and even-anchor construction.

The cofinal choice order is unchanged: finite refutation, horizon t,
growth ordinate F with odd binomial, beta spacing and code, CRT columns
and anchor, radix, then the main Pell frame. There is no circular choice.

## Important integration obligation

Changing t=16+4z^2 to t=64+4z^2 is not a pointwise coordinate substitution
in the old polynomial. It is a semantic cofinal-horizon replacement.
For example one cannot generally recover an integer z_old with
16+4*z_old^2=64+4*z_new^2.

Therefore the final report must explicitly establish that the old source
uses the horizon shape only to supply t>=16, divisibility by four, and
cofinality. Retained finite row/frame identities must be rechecked with
the new literal horizon constant. The ordinary source proof's remaining
estimates and encodings apply uniformly to these new horizons; the
source's exact old horizon row itself is replaced, not reconstructed.

Subject to that explicit semantic-interface check and the exact emitted
row audit, the proposed growth replacement is arithmetically sound and
complete and retains degree four after the sum-of-squares compiler.
