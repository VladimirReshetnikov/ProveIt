# A square transport weight and an integral root center

## Status and exact result

At the pinned ProveIt snapshot `0c48d332df6b0e50d4e5b6251c531898f5682c72`,
this supplement combines the unsquared trace theorem in
`163-trace-radical/compact/PROOF.md` with the inverse-Lucas correction in
`164-unsquared-factors-linear-selectors/positive/PROOF.md`. These two source
proofs and the literal inverse-Lucas parent DAG are retained beside this file.

There are three complete literal polynomials:

| Name | Domain | Variables | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| inverse_trace232_bV | strictly positive integers | 10 | 232 | 85 |
| inverse_trace232_b2 | strictly positive integers | 10 | 232 | 85 |
| centered224 | strictly positive integers | 10 | 224 | 90 |

The first combines two independent improvements. The second resolves the
specific b-squared transport question left open in Section 9 of the trace
paper. The third uses this new transport weight to permit an integral
polynomial root center while retaining positive completeness. It is an
explicit degree/cost tradeoff against the trace paper's degree 232/87 point.
None of these is an equation in ten unrestricted integers.

The ordinary proofs below, composed with the identified inherited
native/refutation calibration, give in ZFC that each equation has a positive
zero if and only if there is a finite syntactic ZFC refutation. We do not
claim a global minimum, historical priority, a new object-language ZFC proof
term, or a fresh full proof-assistant compilation. The small-variable branch
retains its K215/native ancestry. The direct integer equation in the main
research packet is a different construction.

All four fixed coefficients are reconstructed by the included finite
constructor from the retained printed recipe. Both their raw and compressed
hashes match the parent byte for byte. No coefficient is chosen according to
whether ZFC is consistent. The largest port has 592,884 bits; the four raw
payloads together have 295,388 bytes.

## 1. Complete equations

Let the independent variables be

    J,F,alpha,i,T,w,s,n,eta,zeta > 0.

The four fixed ports are beta,K0,MC,MF, specified by
`163-trace-radical/compact/coefficient_recipe.tex` and reconstructed by
`reconstruct_coefficients.py`. In particular beta=2^590069-1. All other
letters below abbreviate polynomials and introduce no variables:

    h=beta J, q=h+1, C0=q-F-alpha,
    X=qw, Y=qs, k=eta+zeta, c=kY+eta,
    A=Y(X+1)+1, Delta=A^2-1, H=4A-5,
    v=XY^2, ell=vk=(XY)(kY), E=1+ell(ell+k),
    R=[h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    B=(K0+w)C0-F,
    U=ic^2, a=Delta U^2 E, F0=1+a,
    f=1+2a, G=E F0, Q=4Delta aF0,
    b=cT-R, V=fb-c, K=X(3c-2X)+2,
    e6=6(k-R-1)-ell(k^2-4), D=6q^6,
    M=hDH,
    Z0=hD[H(n-LB)+K]-H[DB+h(e6-6q^4s)].

For `inverse_trace232_bV`, take L=bV and Z=Z0. For
`inverse_trace232_b2`, take L=b^2 and Z=Z0. For `centered224`, take

    L=b^2, C=AUE, S=CV, Z=Z0-MS.

In all three cases the single equation is

    P=Q(Z^2-M^2 G V^2)+(M^2 G-Z^2)=0.             (1)

The JSON files contain exactly 85,85,90 live binary operations, respectively.
The symbol v is proof shorthand: the literal circuit reuses ell rather than
computing v separately. All powers in the literal DAG are fixed
multiplications. No variable exponent, recurrence, floor, or existentially
unspecified coefficient occurs in the final polynomial.

For the proof only set

    e*=e6/6=k-R-1-vk(k^2-4)/6,
    rho=e*/q^6, sigma=s/q^2, t=B/h, W=1+hL,
    kappa=K/H, z=Z/M.

The exact rational carrier identity is

    z=n+kappa+sigma-Wt-rho                        (uncentered),
    z=n-S+kappa+sigma-Wt-rho                      (centered).       (2)

No quotient is presumed integral at this point.

## 2. Inherited root and index facts used before sign recovery

The changed correction and center do not alter the Pell factors in (1).
The root extraction, rational adjacent-Pell descent, all-index folding, and
third-index exclusions proved in the trace source therefore apply first.
Their precise output, without assuming a sign for B,C0,R,b orV, is:

    q>=32, A>4, c>k>=2, c>X, K>0,
    G=g^2, E=tau^2, F0=f0^2 with g,tau,f0>0 integral,
    z=epsilon g y with y>0 integral and epsilon in {+1,-1},
    Q V^2-(Q-1)y^2=1,
    c=psi_A(p), p>=5 odd,
    k=2psi_(1+2v)(m), m>=2,
    c>8XY^3>=8q^4,
    b!=0, sign(V)=sign(b), Q>f^2, c<f/2,
    |V|>8Q^2 and |b|>8f^3-1/2.                  (3)

For clarity, the trace-specific auxiliary third-index exclusion uses

    f(b-4Delta f)=c-(4Delta+3),
    f(b+4Delta f)=c+(4Delta+3).

Both right sides lie strictly between 0 and 2c<f, because
c>psi_A(3)=4Delta+3. Thus the auxiliary index is at least 5 and gives the
last bound in(3). This argument depends on neither the correction e6 nor
the transport weight L nor the carrier shift S.

Here psi_A(0)=0, psi_A(1)=1,
psi_A(j+2)=2A psi_A(j+1)-psi_A(j). The inherited root extraction follows
from G being coprime to both Q-1 and QV^2-1 and
Q=4Delta^2 U^2 G. The retained proof establishes integrality by descent,
not by presuming that a rational Pell root is integral.

## 3. The new b-squared transport bound

Put C=AUE. Since

    a^2/g^2=Delta U^2 a/(1+a)>Delta U^2/2>9,

one has g<a/3<f/6. Also

    C^2/G < A^2/(A^2-1)<4,

so C<2g. From the adjacent Pell equation in(3),
y<(3/2)|V|. Since c<f/2 and |b|>=1,

    |V|<=f|b|+c<(3/2)f|b|.

Consequently, for either sign epsilon,

    |epsilon g y+CV|
       <=g y+C|V|
       <(7/2)g|V|
       <(7/8)f^2|b|
       <(7/32)b^2
       <b^2/4.                                  (4)

The penultimate inequality uses |b|>4f^2, a strict consequence of(3).
The same bound with CV removed applies to the uncentered b-squared
variant. This is stronger than the bound needed for the sign bootstrap.

Unlike the forward cubic in the trace source, the inverse correction is
nonnegative before any rank sign has been established: k>=2 gives
vk(k^2-4)/6>=0. Therefore

    e*<=k-R-1<b, rho<|b|/q^6<b^2/4.              (5)

If B<=-1, then Wt<-L. Solving(2) for n and applying(4),(5), with
positive kappa and sigma, gives

    n<L/4-L+L/4<0,

a contradiction. Hence B>=0 and C0>0. This treats every integer R,
including negative and zero R, uniformly. It is precisely why the open
b-squared question from the trace source becomes tractable here.

The bV composition instead uses the already proved trace estimate
g y<L/2 and the same inverse-correction inequality(5), as in the
inverse-Lucas source.

## 4. Completion of soundness

Only after B>=0,C0>0 apply the calibrated mask bound
3q<R<q^4-2. It gives c>2R and b,V>0. The literal identities

    f-1=2Delta i^2 c^4E,
    V=-c mod f, V=-R mod c

license the same normalized-rank and auxiliary-index theorem as in the
trace proof. Therefore p=R, R is positive odd, q is even, and J is odd.

In the centered variant S is an integer polynomial. Thus z integral
implies z+S integral, and the subsequent inverse-Lucas argument sees
exactly the same carrier as the uncentered variant. The weight affects
that argument only through W=1+hL, which is 1 modulo h for every L.

For explicitness the inherited expansion is

    k=2m+8v C_m+32v^2 Z_m,
    C_m=binom(m+1,3), Z_m>=0 integral.

Writing d=2m-R-1 and A_m=C_m+4vZ_m gives the exact identity

    3(e*-d)=4v^2[24Z_m-A_m(k^2+2mk+(2m)^2-4)].    (6)

Carrier integrality yields q^6|(e*-q^4s), hence q^4|e*. For each
prime l|q, the right side of(6) has valuation at least6 ord_l(q),
so e*-d has valuation at least6 ord_l(q)-ord_l(3)>=4 ord_l(q).
Thus q^4|d. Comparing the two Pell bases gives1<=m<R, and the
calibrated bound R<q^4 forces d=0.

Do not cancel the possible factor 3 from (6) yet. First the carrier yields
H|6hK. The inherited whole-product projection and strict size bound give
X=2^R. Since q|X, q is a power of 2, and now(6) proves q^6|e*.
It follows that rho is integral. The remaining carrier congruence then
gives q^2|s and h|B, hence sigma integral and t a nonnegative integer.
The other projector gives kappa a positive integer.

This recovers the exact native endpoint

    X=2^R, q^3|Y, t=B/h>=0 integral,
    (K0+w)C0-F=t(q-1).

The retained fixed-minus parity, half-binomial rounding and whole-tuple
native/refutation calibration give a finite syntactic ZFC refutation.
No new coefficient substitution or shortened calibration is made here.

## 5. Positive completeness without a hidden sign assumption

A finite refutation supplies the canonical outer witnesses in the
inverse-Lucas source. In particular q is a power of 2, R=3 modulo 4,
X=2^R, q^3|Y, C0>0, t>=0 integral, c=psi_A(R), and
k=2psi_(1+2XY^2)((R+1)/2). Set s=Y/q and use the inherited interval
to obtain eta=c-kY>0 and zeta=k-eta>0. The already established
congruences make rho,sigma,kappa integral.

Choose a positive strong Pell seed as in the source, giving
c^2 tau|I0, i=I0/(c^2 tau)>0, f0^2=1+Delta I0^2,
f=2f0^2-1, g=tau f0. The source supplies a positive adjacent Pell pair
V*,y with

    V*+c+Rf^2 divisible by cf^2.

The unsquared trace input is

    T=(V*+c+Rf)/(cf)>0.

It is integral because c|(f-1). The identity V*=f(cT-R)-c follows.
For the uncentered variants set

    n=g y+(1+hL)t+rho-kappa-sigma.

The inverse-Lucas source proves |rho|<g/3 and kappa+sigma<g/2;
thus n>0. These bounds follow directly from
g>sqrt(Delta)c^2E>vk^3 and g>4Xc, while
|rho|<vk^3/3, kappa<Xc and sigma<=Y<Xc.

For the centered variant the correct root sign is negative. We must
prove that CV*-g y can be made positive and large. Put u0=U^2E>=2.
The exact identity is

    (Q-1)C^2-QG = E[Q(u0-1)-A^2u0].             (7)

Since Q=4Delta^2 u0(1+Delta u0)>4Delta^2u0 and
4Delta^2>A^2, the right side is positive. Hence

    C>g sqrt(Q/(Q-1)).

The Pell equation implies y<V*sqrt(Q/(Q-1)), so
CV*-gy grows at least linearly with V*. More explicitly, the positive
integer D0=(Q-1)C^2-QG satisfies

    CV*-gy > D0 V*/[2C(Q-1)] >= V*/[2C(Q-1)].     (8)

The existing positive adjacent pair can be made cofinally large without
changing its residue modulo cf^2. Apply the integral norm-preserving matrix

    [2Q-1, 2(Q-1); 2Q, 2Q-1]

to the column(V*,y). It has determinant 1, strictly increases positive
coordinates, and has finite order modulo cf^2. Iterating a period preserves
the required residue and makes V* unbounded. No new variable or constraint
is inserted into the polynomial; this is a completeness choice of T.

Choose V*>2C(Q-1)(kappa+sigma+|rho|) and set

    n=CV*-g y+(1+hb^2)t+rho-kappa-sigma.          (9)

All terms are integers and (8) makes n strictly positive. The centered
carrier is z=-gy, so(1) vanishes. Every independent input has been
constructed in its stated positive domain. This is a zero-existence
equivalence, not an unrestricted shear of all positive assignments.

## 6. Exact cancellation and degrees

For the centered equation C=AUE and

    C^2-G=E(U^2E-1).

Substitution and expansion give the free-polynomial identity

    P=(Q-1)Z0^2-2(Q-1)MCVZ0
       +M^2V^2[QE(U^2E-1)-C^2]+M^2G.            (10)

The degrees of Q,M,V,U,E,Z0,C,G are respectively
80,11,40,7,14,21,25,50. The unique degree 224 term in(10) is
QM^2V^2U^2E^2. The quadratic Z0 term has degree 122 and the mixed Z0 term
has degree 177; the E-only subterm has degree 196 and the C^2 subterm has degree 152.
Thus the naive degree 232 of the unexpanded norm cancels exactly.

Write q0=beta J, k0=eta+zeta and

    B0=k0 sT-q0^2(q0-F).

The complete highest homogeneous component is

    [P]_224=9*2^10 q0^96 w^24 s^56 i^10 k0^32 B0^2.

It is nonzero at the authentic beta>0: the coefficient of
J^96 w^24 s^58 i^10 eta^34 T^2 is9*2^10 beta^96.
The exponents sum to224. For both uncentered variants the complete top is

    [P]_232=-9*2^10 q0^100 w^26 s^58 i^10 k0^32 B0^2.

The independent verifier proves(10) in a free polynomial ring, authenticates
every actual DAG gate through independent polynomial cuts, checks all live
inputs and fixed ports, derives the complete leading forms, verifies both
raw and compressed coefficient hashes, and rejects both alternative binary
operators at every gate. It rejects 180,170,170 targeted corruptions in the
three graphs. These finite checks do not replace the unbounded Pell,
positivity or calibration arguments.

## 7. Further questions

The square transport weight now leaves substantial room in the absolute
bound(4). A shorter root-center schedule, a different strong-index scale,
or a signed-domain analogue could improve the degree/cost tradeoff.
The polynomial AUE is a natural approximation to sqrt(G), but this note
does not establish an optimum among all possible polynomial centers.

The integer direct branch and this positive branch have different costs:
variable count, degree, operation count and fixed-numeral bit length must
be reported together. Converting ten positive inputs to unrestricted
integers by a generic sign representation can erase its advantage; no
such converted equation is promoted as a new optimum here.
