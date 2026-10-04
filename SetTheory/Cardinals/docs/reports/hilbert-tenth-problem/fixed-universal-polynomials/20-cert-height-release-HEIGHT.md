# Quantitative height of the full square/product 82 counterfamily

## Scope and result

This is an independently authored quantitative follow-on to
`BASE_COUNTERFAMILY.md` (recovered proof SHA256
`690c5a1dc237bd53a9582bfbe01fcd8a176174e6b116089a1842532f83c1770b`),
read as data. It concerns precisely that construction, with a fixed genuine
compiler and positive ordinary input x. No upstream program or saved arithmetic
schedule was executed. No full giant witness tuple was materialized.

Write `bl(z)=floor(log2 z)+1` for positive integers. The largest of its 18
witnesses is **y_aux**, and its bit length is exactly

    bl(y_aux) = (R−1)(2pL−1)+1,       L=p+yexp+1.                 (H1)

Thus, putting H equal to the numerical maximum of all 18 witnesses and
N=(R−1)(2pL−1),

    2^N < H=y_aux < 2^(N+1).                                  (H2)

There is no hidden third exponential level: H is doubly exponential in the
chosen radix exponent t. The exact leading coefficients in R are 4/3 in
Branch A and 25/14 in Branch B. The uniform bounds below justify the exact
bit lengths without rounding an asymptotic formula.

This is an upper bound (and exact height) for this particular witness family,
not a lower bound on arbitrary witnesses of the 82 chart. The auxiliary-minimality result in AUX_MINIMUM.md fixes the outer tuple.
Its first theorem fixes i=1 and F_aux=Delta*c^4+1; its second allows
every positive i and proves the same joint minimum. The packet is a new
result pending separate audit, not an amendment to the original
all-input proof or a prior report.

## 1. Parameters and a uniform elementary error bound

Use the notation of the counterfamily. To separate the exponent from the
auxiliary Pell witness, write y=yexp, X=2^p, Y=2^y, and set

    L=p+y+1, C=(p−1)L, F0=4C+2L−2,
    T=2pL−1=2C+2L−1, N=(R−1)T.

In both branches p>I>=3, I is odd, p>=16, y>=3, n>=3, R>=8, R<2p.
The actual construction satisfies these with an enormous margin: t>=625,
p>56t, y>=3t, and R>2^(3t). The relation R<2p follows directly from
Branch A: R=6u−epsilon, p=4u; Branch B: R=28v−1, p=20v.

The exact resonance in the source is equivalently

    L1=p+2y+2,       (n−1)L1=C−y−1,       nL1=pL.               (H3)

Define the positive error d=1/X+2/(XY), so

    2A=2^L(1+d),       0<d<2^(1−p).

For p>=16 the function p^2/2^p decreases, and

    4p^2 * 2^(1−p) = 8p^2/2^p <= 1/32.

Consequently, for every integer 0<=j<=4p^2 and every
0<=z<2^(1−p), the binomial/geometric-series bound gives

    1 <= (1+z)^j <= 1/(1−jz) < 32/31 < 2                    (H4)

when jz>0; the non-strict version covers j=0. The strict 32/31 endpoint
also holds at p=16 because z is strictly below 2^(1−p).
All error exponents used below are at most 4p^2, including
2p(R−1), 4p−2, p−1, and n.

## 2. Exact dominant bit lengths

The source Pell estimates and 2A−1>2XY imply

    2^C < c < 2^C(1+d)^(p−1) < (32/31)2^C.

Also

    2^(2L−2) < Delta < 2^(2L−2)(1+d)^2.

The lower inequality uses Delta=(XY+Y+2)^2−1>(XY)^2.
For S=Delta*c^2, therefore,

    2^(T−1) < S < 2^(T−1)(1+d)^(2p).                       (H5)

Since S is an integer and T is an integer, 2S−1>2^T.
For R>=3 the source bound gives

    y_aux=psi_S(R) >= (2S−1)^(R−1) > 2^N,
    y_aux < (2S)^(R−1)
          < 2^N(1+d)^(2p(R−1)) < (32/31)2^N < 2^(N+1).

This proves bl(y_aux)=N+1 exactly.

For V=chi_S(R)/S, the recurrence gives
chi_S(j)/S >= (2S−1)^(j−1) for j>=1: the successive chi ratios
are >2S−1 starting with chi_S(2)/chi_S(1)=2S−1/S.
Moreover, the norm equation gives

    V^2=(1−S^(−2))*y_aux^2+S^(−2)<y_aux^2.

Thus 2^N<V<2^(N+1) as well.

For the strong-cut witness,

    2^F0 < F_aux=Delta*c^4+1
         < (32/31)2^F0+1 < 2^(F0+1),

where the upper error exponent is 4p−2 and F0>=1.
Therefore bl(F_aux)=F0+1.

For U_aux=(V+R*F_aux)/c+1 we get another exact bit length.
First, because 2Delta−1>2^(2L−1),

    V/c >= (2S−1)^(R−1)/c
        > (2Delta−1)^(R−1)*c^(2R−3)
        > 2^(N−C).

Second,

    V/c < (2Delta)^(R−1)*c^(2R−3)
        < 2^(N−C)(1+d)^[2p(R−1)−p+1]
        < (32/31)2^(N−C).

The remaining positive summand is small enough uniformly. Indeed,

    N−F0=(2R−6)C+(2R−4)L−R+3 >= R,

using C>=15 and R>=8. Since F0>=C, c<2^(C+1),
F_aux<2^(F0+1), and R+1<=2^(R−2),

    R*F_aux+c < (R+1)2^(F0+1) <= 2^(N−1).

Dividing by c>2^C shows

    2^(N−C) < U_aux < (32/31+1/2)2^(N−C) < 2^(N−C+1).

Hence bl(U_aux)=N−C+1 exactly. In particular U_aux<y_aux.

## 3. Bounds for all 18 witnesses

Put lc=ceil(log2(W+Z)); this is an ordinary exact integer bound and
lc<=ceil(t/4)+1. All rows marked '=' are exact bit lengths; '<=' rows
are certified upper bounds. The list is in the source's witness order.

| Witness | Bit length |
|---|---:|
| J | <= t |
| F | <= ceil(t/2)+3 |
| alpha | <= t |
| t_tr | <= p−2t+lc+2 |
| F_aux | = 4C+2L−1 |
| h | = C−p−2y+1 |
| i | = 1 |
| U_aux | = N−C+1 |
| s | = y−3t+1 |
| w | = p−t+1 |
| tau | = pL |
| eta | <= C−p+ceil(log2 p)+3 |
| zeta | <= C−y+1 |
| y_aux | = N+1 |
| Z | <= floor(log2(6t))+1 |
| delta | = (I−3)L+3 |
| rho | = (I−2)L+1 |
| sigma | = (p−2)L+1 |

Every non-auxiliary row has bit length at most F0+1, and
N−F0>=R>=8. Thus y_aux is strictly the largest witness, establishing
(H1)–(H2) for the full tuple, not just an auxiliary subset.

### Justification of the remaining rows

The source gives 0<J,alpha<q=2^t, F<=2^(t/2+2)+2, Z<=6t,
and W+Z<2^(t/4+1). The definitions of s and w give their exact rows.
For transport, q−1>2^(t−1), w−2^e<w, and p>56t, so

    t_tr < 1+2^(p−2t+lc+1) < 2^(p−2t+lc+2).

For the first Pell pair set M0=2^L1=4XY^2 and d1=1/(2XY^2).
Then 2P=M0(1+d1), 2P−1=M0+1, and d1<2^(1−p).
The source estimates and (H3)–(H4) give

    2^(C−y)<k<(32/31)2^(C−y)<2^(C−y+1).

Since n>=3 and M0>=4,

    psi_P(n) >= (M0+1)^(n−1)
              >= M0^(n−1)+(n−1)M0^(n−2) > M0^(n−1)+n.

It follows that k−2n>2*M0^(n−1)=2^(C−y).
Dividing by E=2^(L−1) and using the upper k bound proves
bl(h)=C−p−2y+1.

For tau, the chi recurrence gives

    P(2P−1)^(n−1) < chi_P(n) < P(2P)^(n−1).

(The lower endpoint can be replaced by a non-strict inequality without
changing the argument.) Therefore

    2^(nL1−1)<tau<2^(nL1−1)(1+d1)^n<2^(nL1)=2^(pL),

so bl(tau)=pL. The source ratio bound supplies

    eta<4p*kY/X<2^(C−p+3)*p,
    0<zeta<k,

which proves the displayed eta and zeta upper bounds.

For delta, write d_j=(psi_A(j)−j)/Delta at odd j. The ordinary
Pell recurrence at step two yields

    d_1=0, d_3=4,
    d_(j+2)=(4A^2−2)d_j−d_(j−2)+4j.

Inductively d_j>d_(j−2)>=0, and

    d_(j+2)>(4A^2−3)d_j>(2A−1)^2*d_j.

Thus d_I>=4(2A−1)^(I−3)>=2^[(I−3)L+2],
with equality at I=3 allowed. Conversely,

    d_I<psi_A(I)/Delta
       <2^[(I−3)L+2]*(1+d)^(I−1)<2^[(I−3)L+3].

This proves its exact row including I=3, where delta=4.

For rho and sigma use the source's integer sequence g_j. Its recurrence
and g_2=1 imply, for 3<=j<=p,

    (2A−1)^(j−2)<g_j<=(2A+2)^(j−2).

For the upper bound, g_j>=2^(j−2), hence the inhomogeneous term in
 g_(j+1)=2A*g_j−g_(j−1)+2^(j−1) is at most 2g_j.
The lower bound follows from strict increase of g_j. Now

    2A+2=2^L(1+1/X+3/(XY)),

whose error is <2^(1−p) because Y>=8. Applying (H4) gives

    2^[(j−2)L]<g_j<(32/31)2^[(j−2)L].

This proves rho=g_I has the stated exact bit length. Since I<=p−1,

    sigma=g_p−g_I >= g_p−g_(p−1)
         > (2A−2)g_(p−1) > 2^[(p−2)L],

while sigma<g_p<2^[(p−2)L+1], proving its exact row.

## 4. Exact branch formulas and leading terms

Branch A has z=R+epsilon, p=2z/3, y=z/3−1, L=z. Thus

    bl(H)=(R−1)[(4/3)(R+epsilon)^2−1]+1.

Equivalently,

    epsilon=+1: bl(H)=(4R^3+4R^2−7R+2)/3,
    epsilon=−1: bl(H)=(4R^3−12R^2+9R+2)/3.

Branch B has z=R+1, p=5z/7, y=15z/28−1, L=5z/4. Thus

    bl(H)=(R−1)[(25/14)(R+1)^2−1]+1
         =(25R^3+25R^2−39R+3)/14.

All these are integers under the source congruences. In particular

    bl(H)=(4/3)R^3+O(R^2)   in Branch A,
    bl(H)=(25/14)R^3+O(R^2) in Branch B.

These statements supplement, rather than replace, the exact formulas.
The main Pell witnesses have O(R^2) bits, and the auxiliary Pell witnesses
have Theta(R^3) bits. The input-loader coordinates rho and delta have
O(IR) bits. Although i=1, its paid appearance in S remains untouched.

## 5. Explicit radix and input dependence, with jumps preserved

Let d=5^a be the genuine fixed radix exponent, let kbit=bl(K), and put

    I=ell*x+b, M=max(I,kbit,61),
    r=max(a,ceil(log_5(4M))), t=5^r, q=2^t.                 (H6)

This is the requested minimal r; the redundant source threshold 16 is
absorbed by 61. In particular

    max(d,4M)<=t<=max(d,20M).

When t>d, the upper comparison t<20M is strict.

The packed R is much closer to q^4 than the source's loose q^3 lower
bound suggests. Expanding its exact formula gives

    R=q^4−q^3*F−q^2*(Z+1)+qF+Z+M_mask,

where M_mask is the source's (MC+q*MF)J, not the maximum M in (H6).
Using the source's strict R<q^4 and positivity of the last three terms,

    0<1−R/q^4
      < e_t := 4*2^(−t/2)+2*2^(−t)+(6t+1)*2^(−2t).       (H7)

For t>=625, 6t+1<2^(t/2), so e_t<5*2^(−t/2)<1/100.
Thus R=2^(4t)(1−theta_t), 0<theta_t<e_t. Equations (H1) and
(H7) prove, along the actual construction as t tends to infinity,

    bl(H)=gamma*2^(12t)(1+O(2^(−t/2))),
    log2(log2 H)=12t+log2(gamma)+o(1),

with gamma=4/3 or 25/14 according to the fixed branch. The explicit
formulas (H1), (H6), (H7) contain the constants hidden by this display.

A convenient fully explicit, deliberately loose summary is

    2^(12t)<bl(H)<2^(12t+1),
    2^[2^(12t)]<H<2^[2^(12t+1)].                            (H8)

For completeness: R>=100 and (H7) give R>(99/100)q^4; direct comparison
of the exact cubic formulas gives (5/4)R^3<bl(H)<2R^3.
The lower multiplier (5/4)(99/100)^3 exceeds 1, proving the bit-length
part of (H8). Integer endpoints and (H2) give its height part.

For every x, this implies the explicit compiler-dependent bound

    2^[2^(12*max(d,4M))] < H
       < 2^[2^(12*max(d,20M)+1)].                          (H9)

Eventually, for a fixed compiler, I dominates kbit and 61 and 4I>d.
Then 4I<=t<20I, giving

    2^[2^(48I)] < H < 2^[2^(240I+1)],   I=ell*x+b.          (H10)

It would be incorrect to replace t by a single constant multiple of x
in the leading asymptotic. t is constant over long input ranges and
jumps by a factor of five at radix thresholds. Within such a range R
still depends on x through the packing data. Equations (H6)–(H10)
retain this dependence and make no smooth x-asymptotic claim.

## 6. What the index optimization does and does not improve

The separate AUX_MINIMUM.md proves, for fixed outer coordinates,
i=1, and F_aux=Delta*c^4+1:

* Every auxiliary norm-one solution has an odd Pell index m
* In the actual family 8 divides c, and every negative V is excluded
* Positive V is admissible exactly at m congruent to R or −R modulo c
* c>2R, so the least positive admissible index is exactly R

Therefore taking a modular representative or the least positive
congruence representative cannot shrink the selected auxiliary index.
In particular the unavoidable lower bound within this extension is

    log2(y_aux)>=(R−1)log2(2S−1)>N.

In fact, with the same outer tuple, allowing every positive i also fails
to improve the auxiliary minimum. Since P5=1, a zero requires Na*Qs=1.
But 4 divides S=i*Delta*c^2 and Na is congruent to y_aux^2 modulo 4,
so Na=-1 is impossible. Necessarily Na=Qs=1 and
F_aux=Delta*i^2*c^4+1. The same index classes hold; for m>=R, both
psi_S(m) and chi_S(m)/S strictly increase with S. Thus i=1,m=R
uniquely minimize y_aux and U_aux, and jointly minimize the complete
auxiliary coordinates. The detailed positive binomial-expansion proof is
in AUX_MINIMUM.md.

This does not rule out a different outer construction. A lower bound for
this fixed outer tuple does not imply a lower bound for the whole
polynomial's smallest witness. The tower reduction here is the rigorous recognition
that the complete displayed family already requires only two
exponential levels; it is not an independently proved single-exponential
construction.

## 7. Verification and source boundary

The source proof has been rebound to the fresh recovered proof copied as
BASE_COUNTERFAMILY.md, with its own SHA256 above. It is not presented as
byte-identical to the historical lost proof. All eight restored upstream
snapshots retain their original authenticated pins; they are copied under
source/ and treated only as data. The new checker verifies all nine pins,
the exact 18 supplied witness ports, all six fixed ports, ordinary input x,
and 22 literal auxiliary/finalizer rows, without executing the saved graph.

height_check.py is independently authored, standard-library-only, and
uses explicit failing checks that remain active under Python -O. Both
normal and optimized runs produced byte-identical PASS receipts:

* 3,458 active checks, including two deliberate rejected negative controls
* Six independent inner component fixtures: Branch A u=4,...,8; Branch B v=2
* 74 odd input-loader exponents distributed across these fixtures
* 27 separate diagnostic outer CRT/packing fixtures across all three residues
* 241 exact rational uniform-error cases and 401 cubic-squeeze cases
* Largest materialized integer: 307,945 bits, below a hard 500,000-bit cap

The inner and outer fixtures are disjoint. No complete witness tuple was
materialized. Diagnostic mask tuples are not genuine compiled programs.
The unbounded conclusions are proved by the argument above, not by the
finite checks. HEIGHT_CHECKS.json and HEIGHT_CHECKS_O.json are the receipts.

auxiliary_minimum_check.py was also hardened to explicit checks rather
than assert statements. Its normal and optimized PASS receipts are
byte-identical (AUX_CHECKS.json and AUX_CHECKS_O.json); AUX_MINIMUM.md
explains that separate checker's scope. A separate mathematical audit is
still pending. The analytic expansion/inversion work, if any, is outside
this core packet's verified claims until separately completed and audited.
