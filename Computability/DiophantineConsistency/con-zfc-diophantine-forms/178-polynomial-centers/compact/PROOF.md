# Square transport and polynomial centers for the folded Pell equation

AI-assisted research prepared for Vladimir Reshetnikov and ProveIt,
25 October 2026. Comparison snapshot:
`fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb`.

## 1. What is new and what is inherited

All ten independent coordinates in this component range over **strictly
positive integers**. The fixed four-number coefficient tuple is the complete
directly indexed BFS943/radix67 tuple of the pinned parents, used together.
The new construction does not replace that calibrated tuple by arbitrary
numbers satisfying elementary bounds. It retains the native/K215 ancestry.

| Literal circuit | Operations | Exact total degree | Carrier weight | Polynomial center | Root scale r |
|---|---:|---:|---|---|---:|
| `trace_inverse85.json` | 85 | 232 | bV | 0 | 1 |
| `square_transport85.json` | 85 | 232 | b² | 0 | 1 |
| `lower_center87.json` | 87 | 228 | bV | (A−1)UE | 1 |
| `centered_transport88.json` | 88 | 224 | bV | AUE | 1 |
| `quotient_center96.json` | 96 | 220 | bV | 2AUE−UQE | 2 |

The first row composes two already proved mechanisms: package 163's explicit
trace and package 164's inverse-Lucas correction. The second resolves the
specific unproved `L=b²` extension identified in package 163, section 9.
The inverse correction supplies the missing uniform signed bound. That
stronger absolute transport bound also admits the new polynomial centers.
For `AUE`, an exact cancellation lowers degree from 232 to 224; a polynomial
quotient improves the defect and lowers degree again to 220. The bV weight
lets the implementation share the factor V in the carrier. In the
retained family this gives a new cost/degree choice; it is not a theorem of
global minimality or literature-wide novelty.

Ordinary mathematical proofs of the new steps are given below. The inherited
Pell folding, normalized-index, ratio, native reconstruction, and syntactic
refutation calibrations are precisely those used in the two retained parent
proofs. The resulting statement, with those identified inherited results, is

    ZFC proves: P has no positive-integer zero iff Con(ZFC).

Neither an actual zero nor the absence of zeros is asserted. No new
end-to-end Lean/Rocq artifact or encoded object-language ZFC proof term is
claimed. The exact finite checker authenticates polynomial definitions and
identities; it does not prove the unbounded arithmetic lemmas by testing.

## 2. Complete definitions

The ten independent variables, in their literal JSON order, are

    J, F, alpha, i, T, w, s, n, eta, zeta > 0.

The constants are `beta,K0,MC,MF` from the whole parent tuple. The elementary
inequalities used below are

    beta >= 31 odd, K0 > 0, 0 < MC < beta < MF < 2 beta.

They are necessary numerical facts about that tuple, not its calibration.
Every named quantity in this section is an ordinary polynomial abbreviation,
not an extra quantified variable. Put

    h=beta J, q=h+1, C=q-F-alpha,
    X=qw, Y=qs, k=eta+zeta, c=kY+eta,
    A=Y(X+1)+1, Delta=A²-1, H=4A-5,
    ell=(XY)(kY), E=1+ell(ell+k),
    R=[h(q-F)+alpha](q²-1)+(MC+qMF)J,
    B=(K0+w)C-F,
    U=ic², a=Delta U²E, F0=1+a, G=EF0,
    f=1+2a, Q=4Delta aF0,
    b=cT-R, V=fb-c, K=X(3c-2X)+2,
    e6=6(k-R-1)-ell(k²-4), D=6q⁶,
    M=hDH.

For the last row only, define the ordinary polynomial

    QE=(kY)[ell+k-(kY)(Y+1)].

Choose `(L,Cstar,r)` from the table, and define

    Z=hD[H(n-LB-Cstar V)+K]-H[DB+h(e6-6q⁴s)],
    P=Q(Z²-r²M²GV²)+(r²M²G-Z²).                  (2.1)

The requested single ordinary Diophantine equation is `P=0`. The literal DAG
uses only addition, subtraction, multiplication, and fixed integer constants.
Squares and scalar multiplications count as binary operations. There is no
division, variable exponent, factorial, sequence operator, or unspecified
predicate in the polynomial.

For proof only, define rational quantities

    v=XY², e*=e6/6=k-R-1-vk(k²-4)/6,
    rho=e*/q⁶, sigma=s/q², t=B/h,
    kappa=K/H, z=Z/M, W=1+hL.

At arbitrary positive inputs, before any divisibility claim,

    z=n+kappa+sigma-Wt-rho-Cstar V,                (2.2)
    P=(Q-1)Z²-r²M²G(QV²-1).                      (2.3)

These are rational identities used in the proof, not division instructions
in the delivered equation.

## 3. Inherited root extraction, with hypotheses checked before signs

The elementary positive-domain inequalities are independent of the chosen
weight and center:

    q>=32, X,Y>=q, k>=2, c>kY, A>4, U>=c²,
    a>c, f>2c, Q>c², and M>0.

The polynomial identities

    f²=1+4aF0,
    Q=Delta(f²-1)=4Delta²U²G,
    f-1=2Delta i²c⁴E                              (3.1)

remain exact. If `b=0`, then `V=-c`; otherwise `|V|>=f-c>1`. Thus V is
nonzero and `QV²-1` is positive. Since Q is a multiple of G, both Q−1 and
QV²−1 are relatively prime to G. Taking prime valuations in (2.3) at a zero
therefore shows that G is a square. Also gcd(E,F0)=1, because
`F0=1+Delta U²E`. Consequently there are positive integers

    E=tau², F0=f0², G=g², g=tau f0.

For clarity, the square conclusion is valid even though z is initially
rational: use the integer equation (2.3); the valuation of the factor M² is
even, as is the valuation of r². Put `y=|z|/(rg)`. Then

    QV²-(Q-1)y²=1.                                (3.2)

The parent's adjacent-coefficient Pell descent proves y integral. Its
argument applies to a rational y: in lowest terms r/m, m² divides Q−1;
the norm-preserving descent reduces the positive first coordinate |V| while
preserving the reduced denominator m, ending at 1. Thus m=1. In particular,

    z=epsilon rgy, with epsilon in {−1,+1}.        (3.3)

Now set I=2Ug. Equations (3.1) give

    f²-Delta I²=1, Q=(Delta I)², c² divides I, c<=I.

The retained signed all-index folding theorem applies to these facts and
`V=-c mod f`, yielding

    c=psi_A(p), with p>=1 odd.

Here psi is the usual Pell ordinate sequence. The first norm gives
`k=2psi_(1+2v)(m)` with m>=1. The case m=1 places c strictly between the
first two possible positive main ordinates, so m>=2, whence

    k>=8v+4, c>8XY³>=8q⁴, c>X, K>0.              (3.4)

The retained exclusion of p=3 uses q|X,Y, q>=32 and the exact remainder
formula in the parents; neither its proof nor any preceding step uses the
signs of B, C, R, b, or the selected center. It gives

    p>=5 and c>c3:=4Delta+3.                       (3.5)

The shift by Cstar V changes only Z. Root extraction requires only that
Z/M is the rational number occurring in (3.2). Thus every step so far is
valid for all the new circuits, without borrowing a conclusion whose proof
depends on B>=0.

## 4. Strong bounds from the auxiliary index

First b cannot vanish. Otherwise V=−c, and (3.2) would make

    y²-c²=(c²-1)/(Q-1)

strictly between 0 and 1. Hence b is nonzero, V has the sign of b, and
`|V|>|b|`. In particular bV is positive.

The strong-root identities give

    a²/g²=Delta U²*a/(1+a)>Delta U²/2>9.

Thus a>3g and

    g<f/6.                                        (4.1)

Classify the adjacent Pell solution (3.2) at the parameter Delta I.
The auxiliary index is odd; index 1 would give |V|=1. At index 3 one
would have V equal to either sign of `4Q-3`. The two exact rearrangements
are respectively

    f(b-4Delta f)=c-c3,
    f(b+4Delta f)=c+c3.

By (3.5), both right sides are strictly between 0 and 2c<f. Neither can
be divisible by f. Therefore the auxiliary index is at least 5, and

    |V|>=16Q²-20Q+5>8Q².

Since Q>f² and c<f/2,

    |b| >= (|V|-c)/f > 8f³-1/2 > 4f².            (4.2)

Also, directly from (3.2) and `V=fb-c`,

    y<3|V|/2,
    |V|<=f|b|+c<3f|b|/2.                         (4.3)

These are absolute bounds; both signs of b and V are covered.

For the two unscaled nonzero centers, use `G=E+Delta(UE)²`. Then

    (AUE)²/G < A²/Delta < 9/4,

so `0<(A−1)UE<AUE<3g/2`. The zero center satisfies the same weak
upper bound. The quotient center obeys `0<Cstar<2AUE`; a direct proof is
given in section 8. Hence every selected center satisfies
`0<=Cstar<3rg/2`. From (4.1)–(4.3),

    rgy+|Cstar V| < 3rg|V|
                   < rf|V|/2
                   < 3rf²|b|/4
                   < 3r b²/16.                   (4.4)

For L=bV, the same earlier inequality and (4.2) also give

    rgy+|Cstar V| < rf|V|/2 < r bV/8.             (4.5)

Here bV=|b||V|, so no sign has been assumed. All selected variants
therefore satisfy the convenient uniform bound

    rgy+|Cstar V| < 3L/8.                         (4.6)

These are the key new estimates. Both weights dominate the possible signed
Pell value and the extra polynomial center. Square transport is a valid
endpoint in its own right; sharing V makes bV cheaper for the centered ones.

## 5. Recovering B>=0 uniformly, with no negative-rank exception

Because k>=2, the inverse correction satisfies

    vk(k²-4)/6 >= 0.

This inequality is valid independently of R, including R=0 and all
negative R. Moreover `b-(k-R-1)=cT-k+1>0`, so

    e*<=k-R-1<b, and rho<|b|/q⁶.                 (5.1)

Suppose B<=−1. Since W=1+hL and h>0,

    Wt=B/h+LB < -L.

Solve (2.2) for the positive input n and use kappa>0, sigma>0,
(3.3), (4.6) and (5.1):

    n=epsilon rgy+Cstar V-kappa-sigma+Wt+rho
      < 3L/8-L+|b|/q⁶
      < 3L/8-L+L/2 < 0.

The penultimate inequality uses q⁶>2 and L>=|b|, valid for b² and bV.
This contradiction proves B>=0 uniformly, including the scaled endpoint.

Since F>0 and K0+w>0, the identity B=(K0+w)C−F now forces C>0. Only
at this point are the authenticated mask estimates used:

    3q<R<q⁴-2.

Together with c>8q⁴, they give c>2R and therefore b,V>0. The normalized
strong-index theorem and the signed auxiliary-index theorem identify p=R.
Their two residues remain exactly

    V=-c mod f,
    V=-R mod c,

because (3.1) gives f=1 mod c. The center and the choice of L do not enter
these residues. Thus R is positive odd; parent mask parity gives q even
and J odd.

## 6. Correct integrality and projection order

For every circuit, `Cstar V` is an integer polynomial before any equation
is imposed. Consequently integrality of z in (2.2) gives exactly the same
fractional-part relation as the inverse-correction parent. Nothing in the
following argument assumes rho or sigma integral prematurely.

The retained unbounded Lucas expansion is

    k=2psi_(1+2v)(m)=2m+8v Cm+32v² Zm,
    Cm=binom(m+1,3), Zm a nonnegative integer.

As k is even, k(k²−4)/6 is integral, so e* is integral at a zero. Clearing
(2.2), using gcd(q,hH)=1, gives

    q⁶ divides e*−q⁴s, hence q⁴ divides e*.        (6.1)

Set `d=2m−R−1`, `Am=Cm+4vZm`, and
`Sm=k²+k(2m)+(2m)²−4`. The exact cubic-difference identity is

    3(e*−d)=4v²(24Zm−Am Sm).                     (6.2)

Since v=q³ws², its right side is divisible by q⁶. For each prime l|q,
the possible loss of ord_l(3) is at most one, and
`6 ord_l(q)−ord_l(3) >= 4 ord_l(q)`. Thus q⁴ divides e*−d, and (6.1)
implies q⁴|d. The first Pell base 1+2v exceeds A, whereas c>k. The
retained monotonicity argument therefore gives m<R. Hence
`|d|<R<q⁴`, forcing

    m=(R+1)/2.                                    (6.3)

One must not yet cancel the factor 3 in (6.2) to claim q⁶|e*. The next
step removes that obstruction. Reducing the literal carrier numerator
modulo H gives H|6hq⁶K, hence H|6hK. The integer polynomial center is
already multiplied by H, so this reduction is unchanged.

Write R=2r+1. The inherited uniform ratio estimate and (6.3) give
`Y>X^r/3` and `X^(r+1)<H`. The universal Pell projection produces

    H divides 6h(X−2^R)(2^R X+1).

The parent's complete-product strict bound applies on the same domain
X>=32 and r>=48, forcing X=2^R. In particular q is a power of 2 because
q|X. Now 3 is relatively prime to q, so (6.2) with d=0 proves q⁶|e*.
Thus rho is integral, and the projection also gives positive integral
kappa. Finally (2.2), with its integer center, yields q²|s and h|B,
because W=1 mod h. Consequently

    X=2^R, q³|Y, and B/h is a nonnegative integer.

These are exactly the native outer endpoint conditions. The retained
fixed-minus parity, half-binomial rounding, fresh native reconstruction and
whole-tuple logical calibration yield a finite syntactic ZFC refutation.
No step uses integrality of rho before the dyadic-radix conclusion licenses
it, and no positive coordinate is silently allowed an arbitrary integer shift.

## 7. Constructive positive completeness

Conversely, a finite syntactic ZFC refutation supplies the parent's canonical
outer data. In particular q is a power of 2, X=2^R, q³|Y, C>0, and
t=B/h>=0 is integral. The exact ratio theorem constructs positive eta and
zeta, with the required k and c, and the Pell period construction supplies
the strong seed and the positive auxiliary pair. The unsquared-trace parent
then constructs positive V,y and an integer

    T=(V+c+Rf)/(cf)>0

for the literal trace-linear expression V=f(cT−R)−c. All source definitions
outside the carrier are unchanged.

The inverse-correction parent proves, for every canonical strong period seed,

    g>kappa+sigma+|rho|.                           (7.1)

Its proof is independent of the weight and of V: the inverse correction has
`|rho|<vk³/3<g/3`, while kappa+sigma<g/2. In particular it handles rho
of either sign. For the selected weight and center define

    n=rgy+Cstar V+(1+hL)t+rho-kappa-sigma.         (7.2)

Every term is integral. Since y>=1, t>=0, Cstar>=0 and the canonical V
is positive, inequality (7.1), together with r>=1, implies n>0. The literal
carrier then has z=rgy and (3.2) makes P vanish.

This is an existence construction on positive coordinates, not a claim that
an arbitrary integer shear preserves positivity. It works whether or not
refutations exist. Together with section 6 it proves the stated equivalence
of existence of a positive zero and finite syntactic refutability.

## 8. Exact degree: cancellation, not a naive DAG estimate

For every centered variant let Z0 denote the same carrier with its center
set to zero. Then Z=Z0−MCstar V. Put Gbar=r²G and
`S=Cstar²−Gbar`. The exact complete-output identity is

    P=(Q−1)Z0²−2(Q−1)MCstar VZ0
      +M²[(Q−1)S−Gbar]V²+M²Gbar.                 (8.1)

For Cstar=AUE,

    S=(UE)²−E.                                    (8.2)

For Cstar=(A−1)UE,

    S=−2(A−1)(UE)²−E.                            (8.3)

These identities hold in the free integer polynomial ring; they are not
consequences valid only at zeros.

For the final scaled center, exact polynomial division gives

    E=A QE+RE,
    RE=1+k²Y(Y+1)[Y(Y+1)-1].                     (8.4)

This is checked by substituting A=Y(X+1)+1 and ell=XY²k into the literal
QE above. The remainder RE is positive on the entire positive domain.
Also QE>0, because the bracket divided by k is
`(X−1)Y²−Y+1>0`. Therefore `0<QE<E/A`. It follows that

    0<C2:=2AUE−UQE<2AUE.

The exact defect identity is

    C2²−4G=4U²E RE+U²QE²−4E.                    (8.5)

Here RE has degree 10 and QE has degree 10. The first term in (8.5) has
degree 38; the other two have degrees 34 and 14. This supplies the degree
gain while keeping an ordinary integer polynomial center and the fixed
square scaling r²=4. No variable denominator is introduced.

For the q-linear inverse chart the exact
degrees are

    deg(Q,M,G,V,UE,Z0)=(80,11,50,40,21,57).

All three nonzero centers have degree 25. Equation (8.2) has degree 42;
equation (8.3) has degree 46, and (8.5) has degree 38. The five degree bounds for the terms in
(8.1), splitting the inner difference, are respectively

    194, 213, 228, 152, 72    for center (A−1)UE,
    194, 213, 224, 152, 72    for center AUE,
    194, 213, 220, 152, 72    for center C2 and root scale 2.

The maximum is unique in each list. This proves a global degree upper
bound and identifies the whole leading homogeneous component. Define

    q0=beta J, k0=eta+zeta,
    B0=k0 sT−q0²(q0−F).

Then the complete highest components are

    [P232]232 = −9·2^10 q0^100 w^26 s^58 i^10 k0^32 B0²,
    [P228]228 = −9·2^11 q0^98  w^25 s^57 i^10 k0^32 B0²,
    [P224]224 =  9·2^10 q0^96  w^24 s^56 i^10 k0^32 B0².
    [P220]220 =  9·2^12 q0^94  w^22 s^56 i^10 k0^32 B0².

All are nonzero polynomials for the actual positive beta. The degree-224 line,
for example, has nonzero coefficient `9·2^10 beta^96` at
`J^96 w^24 s^58 i^10 eta^34 T²`. The tie in the leading terms of cT and R
is retained in B0; dropping that tie would give an incomplete leading form.

The uncentered b² carrier has exact degree 21, versus 57 for bV. Both
carrier degrees are low enough for the center-defect term to dominate;
the selected centered circuits use bV to share arithmetic. A naive
unexpanded degree propagation through the centered output would only give
232, missing the exact cancellation in (8.2), (8.3), or (8.5).

## 9. Literal costs and verification boundaries

Starting from the pinned 85-operation inverse-Lucas circuit, replacing
`Fsqr=f²` by the already expressible `trace_f=a+F0` costs the same one
addition. Replacing bV by b² costs the same one multiplication.

For the centered bV cases the identity
`n-bVB-Cstar V=n-V(bB+Cstar)` shares one multiplication. The original
three-gate carrier center becomes four gates, plus the cost of Cstar.
For (A−1)UE the register A−1 is already live, so the total is 85+1+1=87.
For AUE first form `A=(A−1)+1`, giving 85+1+2=88. For C2 the literal
QE costs four gates, the center costs five, factoring costs one extra,
and scaling G by 4 costs one: 85+4+5+1+1=96. No hidden gate or
additional witness appears in this accounting.

`verify.py` imports no producer or parent verifier. It checks topology,
all-coordinate/port/gate liveness, exact formula cuts covering every actual
gate, the complete parent transformation, the whole fixed coefficient tuple,
both center-defect identities, the full output identity, exact homogeneous
leading forms and targeted corruptions. The producer independently rebuilds
the literal graphs from the pinned parent JSON.

The main checker requires coefficient payloads. Its explicitly labeled
`--skip-coefficients` switch is a development-only partial check, not a
complete authentication of a fixed Con(ZFC) instance. A final release must
run without this switch after authenticating the four exact coefficient
integers and their inherited native calibration.

The mathematical dependence on the two parent proofs remains explicit.
In particular the checker cannot infer Pell classification, unbounded
completeness, syntactic calibration, or Con(ZFC) from a finite test suite.
