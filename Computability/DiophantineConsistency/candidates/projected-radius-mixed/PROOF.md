# A mixed-domain parent for the projected667 source

Every coordinate of `equation.json` ranges over the unrestricted integers.
Let P be the frozen667-natural system in `source/natural667.json` and Q
the new994-integer system. Then

    (exists z in Z^994, Q(z)=0) iff (exists x in N^667, P(x)=0).

Here each equation is the sum of the squares of its complete listed
quadratic rows. The ordinary refutation calibration of P is inherited
without change. The proof below establishes the new domain conversion;
it does not prove consistency or claim a new Lean/internal-ZFC endpoint.

## 1. Actual-row sign and restoration certificates

Q keeps every one of P's585 rows verbatim. It keeps109 of the previously
used161 quadratic nonnegativity guards, each with three private integer
coordinates:

    x=a^2+b^2+c(c+1).

The right side is nonnegative for all integers. Conversely every natural
x has this representation by Legendre's three-square theorem applied to
4x+1, exactly as in the frozen integer parent. No polynomial substitution
is made into an old residual.

The omitted52 guards are precisely21 oriented power quotients, both
comparison-progression quotients for each of15 seed indices, and the
common comparison-base quotient. They are identified by actual raw
arithmetic roles and bound to their contracted coordinate indices; they
are not arbitrary variables selected by a name heuristic in the checker.

From the109 retained guards,424 independently checked original-row sign
inferences prove533 original coordinates nonnegative. Each inference is
an entire row identity c*x=F with c>0, where either F has positive
coefficients and every odd-power operand was already proved nonnegative,
or F is an explicitly verified affine square. An even power of an
arbitrary integer needs no sign premise. The remaining134 coordinates
are exactly the52 omitted quotients,30 comparison coordinates S/R,
and52 private products. In particular, no power base, exponent, output
or other semantic-prefix coordinate is among them.

The full raw system has1259 coordinates and1177 rows. Its592 omitted
affine wires have stored positive-affine restoring polynomials in the
667 coordinates. Every omitted coordinate is a defined wire, and all
definitions are triangular and monic. Substitution into every raw row
gives exactly the585 retained rows and zero defining rows. This gives
integer restoration, without any sign assumption. The sign certificate
then proves that every one of the643 raw semantic-prefix coordinates
is natural. Thus soundness has not smuggled a natural-domain hypothesis
through an integer restoring polynomial.

The complete raw row partition is39 semantic constraints,109 private
Pell/power constraints and1029 defining gates. Every semantic constraint
uses only the643-coordinate prefix. All142 private free coordinates
have listed reconstruction roles. No private certificate coordinate
enters any of the21 power arguments or outputs. The independent checker
compares every private constraint to the exact local arithmetic
interface, including the single derived index pair.

## 2. Bounds before any power interpretation

Write the actual shared frame and auxiliary coordinates as

    W=2+sum(distinct requested base,exponent,output coordinates),
    Z=z0+1,
    A^2-W^3(W+2)Z^2=1,
    U^2-(A^2-1)V^2=1,
    V=(product over seed j of Y_j^2)*(v0+1),
    B=1+4V(q4+1),
    B-A=U*bq.

The initial sign certificate proves that W,A,z0,U,V,v0,q4 and every
power argument/output are nonnegative. It also proves all seed X,Y and
YminusK nonnegative. Literal constructor identities prove every
requested exponent k positive; this does not assume the truth of any
power. Each actual base n has a retained natural modulus T satisfying

    2*A*n=T+n^2+1.

Consequently n=0 is impossible. Each requested n,k is at least1,
W>=2, Z>=1, and W is strictly greater than every requested n,k,m.

The bootstrap norm is a positive Pell solution at base W+1 with ordinate
WZ. In the standard Pell classification let its index be l. Since its
ordinate is positive, l>0. Base-one reduction gives Y_l(W+1)=l modW;
hence W divides l and l>=W. Pell growth yields

    A=X_l(W+1)>W^W.

In particular A>=2 and A>n,m. The exact identity

    T-(2A-2)=(n-1)(2A-n-1)

proves T>=2A-2>A. Also n,k<W implies n^k<W^W<A. Therefore

    0<=m<T,    0<n^k<T,    T>0.

All these facts precede any interpretation of a candidate power output.
No factorial or CRT-product meaning is used in deriving them.

For each seed, the actual bound row is Y=k+YminusK, so Y>=k>=1.
The product equation for V gives V>=1 and Y^2 divides V. The auxiliary
norm with nonnegative U implies U>=A>=2. Moreover B>=5,
B=1 mod4Y, and B=A modU. These are exactly the main-domain hypotheses
needed by the signed index theorem.

## 3. Signed comparison coordinates recover the true indices

For each seed the exact remaining rows are

    X^2-(A^2-1)Y^2=1,
    S^2-(B^2-1)R^2=1,
    S-X=U*sq,
    R-k=4Y*rq.

Here S,R,sq,rq can be negative. The first norm and X>=0 give X>=1.
Apply the signed-index theorem reviewed in
`PROPOSAL_REVIEW_SHARED_PELL1873_SIGNED.md`, with the exact hypotheses
proved above. This theorem derives signed-abscissa recovery using a
half-period shift; it does not apply the natural Matiyasevic criterion
directly to signed S/R. Its conclusion is

    X=X_k(A),    Y=Y_k(A).

The endpoint i=n and Y=1 are allowed. The single non-seed pair is the
literal t+1 addition formula from its earlier seed pair and the pair
at index1. Its full polynomial identities are checked, so it too is
the true positive pair. Thus every one of the16 requested exponent
groups has the correct Pell coordinates.

For any requested n,k, evaluation of
(A+sqrt(A^2-1))^k at sqrt(A^2-1)=-(A-n) in Z/TZ is legitimate because

    (A-n)^2=(A^2-1) modT.

It gives X_k(A)-(A-n)Y_k(A)=n^k modT. The actual power row

    X+nY-AY-m=T*h

therefore gives m=n^k modT. The strict bounds in Section2 imply
m=n^k as ordinary integers. All21 proposed powers are now true at
their actual natural arguments. Sharing their private witnesses has
not changed the represented relation.

## 4. The22 oriented quotients are nonnegative pointwise

These additional sign facts are useful but are not assumed by the
signed index theorem. Positive main norm gives
X>(A-1)Y: indeed A^2-1>(A-1)^2 and Y>0. Since n>=1,

    X-(A-n)Y-m > -m > -T.

As this equals T*h with integer h and T>0, it forces h>=0. This
establishes all21 actual power-quotient signs without using an
orientation of the old comparison residues.

Similarly U>=A and B>0 imply bq>=0 from B=A+U*bq: if bq<=-1, then
B<=A-U<=0. These22 signs license22 further actual-row product
inferences. There are then577 nonnegative original coordinates; the
remaining90 are precisely30 S/R values,30 S/R quotients and their30
private products. We do not assert that those90 actual values are
natural. Negative local certificates satisfying the signed theorem
exist.

## 5. Explicit common-base lift and fresh positive comparisons

It remains to produce a natural P-witness, rather than pretend that the
given integer witness was natural pointwise. Keep A,U,V,W,Z, all seed
X/Y values, all power ports and every semantic-prefix value. Define

    tLift=A+1,
    q4'=q4+U*tLift,
    bq'=bq+4V*tLift,
    B'=B+4VU*tLift.

The complete polynomial identities in `COMPARISON_NORMALIZATION.json`
show

    B'=1+4V(q4'+1),
    B'-A-U*bq'=B-A-U*bq=0.

All q4',bq' are natural, and B'>A. In particular B'=A modU and
B'=1 mod4Y for every seed. This lift uses an already-soluble comparison
progression; it needs neither a fresh CRT existence argument nor an
unproved assertion that U is odd.

For each seed define the new comparison values

    S'=X_k(B'),    R'=Y_k(B').

Polynomial base-congruence transfer and B'=A modU give S'=X modU.
Reduction at base1 gives R'=k mod4Y. The nonnegative Pell recurrence
is monotone in its base, so B'>A gives S'>=X. The ordinary index bound
gives R'>=k. Hence the exact quotients

    sq'=(S'-X)/U,    rq'=(R'-k)/(4Y)

are natural integers. Their norm at B' is1. Use these new values in
the15 comparison certificates, and recompute every private defining
gate in its stored triangular order.

The complete private-use ledger proves that this modification changes
no semantic row, power argument/output or other arithmetic macro.
All142 private free inputs now have natural values: the unchanged main
coordinates/gaps/moduli were already natural, h and bq were proved
nonnegative, q4',bq',S',R',sq',rq' have just been constructed, and the
discriminant is A^2-1. Every ordinary gate has a positive-coefficient
recipe and every exceptional signed gate is an exact square. Its new
output is therefore natural. The109 private constraints hold by the
listed identities, norms and recovered powers. The39 semantic rows
hold because their entire prefix is unchanged. This is a natural zero
of the full raw system, hence of P by its exact affine projection.

Conversely any natural zero of P, viewed over the integers, satisfies
every original row and extends to the109 private guards by the
three-square representation. Thus it extends to a Q-zero. This proves
the asserted existence equivalence in both directions.

## 6. Literal quartic and scope

Q has994 integer coordinates and694 quadratic rows. Its independently
collected sum of squares has5177 nonzero monomials, maximum absolute
coefficient63905862 and exact degree4. Every coordinate occurs. The
109 guards add327 private coordinates, rather than the old161 guards'
483, saving156 coordinates and52 rows at this unprojected stage.

This994-variable parent is not claimed to beat the existing862-variable
projected integer equation. A new signed monic projection could be
applied only after the domain theorem above is established and would
need its own full restoring certificate. No such projection is counted
here. The improvement being certified is the smaller sound domain
conversion, with explicit handling of its signed-private boundary.

All source bytes, arithmetic/calibration dependencies and verification
programs are pinned. Python checks establish complete finite algebra
and call/domain ledgers; the unbounded Pell argument and normalization
proof are supplied in this note. Lean remains paused. No arbitrary
internal-omega transfer, consistency assumption or non-solution claim
is introduced.
