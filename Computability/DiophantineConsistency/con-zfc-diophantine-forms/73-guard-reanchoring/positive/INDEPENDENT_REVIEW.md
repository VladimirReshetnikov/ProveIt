# Independent review of the adaptive and centered equations

Reviewed the literal graphs, the ordinary argument in `PROOF.md`, the
source61 interfaces pinned at ProveIt commit
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`, and the independent exact
checker `check_new.py`.

**Finding:** no gap found in either new local existence reduction.  This
is a separate AI-assisted mathematical review within the same research
session.  It is not external peer review or a proof-assistant certificate.

## Adaptive thirteen-variable carrier

The argument uses the submodulus q^4, not coprimality of the whole adaptive
carrier U=q^2Y.  From A0=0 one has q^3 dividing Y and gcd(q,H)=1.
Thus q^5 divides U and q^4 divides qXY.  Integrality of the main root
gives U dividing H(qXY-r0), which implies q^4 divides r0.  The inherited
strong/auxiliary index argument yields p=R before q divides X is needed.
The first-Pell recurrence and the strict bound R<q^4 then force
2n=R+1.  Hence 4XY^2 divides r0.  Since q^3 divides Y, the same r0 is
divisible by U.  Dividing U|HqXY by qY gives q|HX, hence q|X.

This order of inference avoids a circular appeal to q|X and avoids the
false stronger assumption gcd(U,H)=1.  The source gamma is reconstructed
integrally; main-Pell growth makes it positive.  For completeness,
r0/U>=4wsq^2>w for X=qw and Y=sq^3, so the new gamma is positive without
needing the stronger source estimate gamma_old>w.

## Twice-centered twelve-variable norm

For every positive input, M>1.  Thus B=2(M^2-1)(M*nu-1) cannot vanish,
even if the polynomial abbreviation nu is negative.  At N=0 the ratio
f=A/B has integer square D, so f is an integer.  With t=nu-f and
y=Mt-1, the exact identities in the proof give

    M^2V^2-(M^2-1)y^2=1.

Here V=Db-c always has |V|>1 because b is an integer, c>=3, and
D>c+1.  Consequently |y|>|V| and u=|y|-V is strictly positive.
Replacing f by |f| and y by |y| preserves all required squares.  These
observations handle the exceptional denominator and both possible signs
without an unproved positivity premise on nu, f, or y.

For completeness, the canonical odd-index Pell witness has
y=-1 modulo M^2, so nu=f+(y+1)/M is integral.  Write
lambda=(a+2)I.  The proof's exact relation

    n=f-lambda+(u+b-c+1)/M

follows from D-1=MI and V=Db-c.  The inequalities M>lambda,c,
D<M^2, R>=7, and V>=M^(R-1) imply b>M*lambda+c, so n>f>0.
This is a canonical witness construction, not an assertion that every
arbitrary old witness has positive n.  The required even old j is
available because the source native repunit J is 1 modulo 6; that
restriction is now explicit in the proof.

The product finalizer is sound: A0,A1,N are squares modulo 4, so none
can equal -2.  If the three integer factors (1+A0),(1+A1),(1+N) have
product 1, each is a unit and none is -1; all are 1.

## Finite algebra and metrics

`check_new.py` reads the literal graph without importing a builder.
Its exact sparse arithmetic checks the carrier prefix, the complete
875-term centered norm, the recovery identities, graph liveness, and
the finalizers.  The checked results are:

| Equation | Positive unknowns | Exact degree | Live binary operations |
|---|---:|---:|---:|
| Adaptive P13 | 13 | 30 | 92 |
| Centered P12 product | 12 | 110 | 105 |
| Centered P12 sum of squares | 12 | 164 | 104 |

In particular the norm's weighted degree is 82, with leading form
4a^12*c^20*i^10*b^2, after the degree-86 cancellation.  Nonzero
selected coefficients certify the final degrees after specialization
of the fixed ports.  I reran the independent checker successfully.

## Scope

The new arguments preserve the positive-domain source equations and
their complete coefficient tuple.  They do not replace or independently
formalize the inherited native compiler, calibration of its accepting
computations to ZFC refutations, or an internal object-language ZFC
derivation.  They do not claim a global optimum.
