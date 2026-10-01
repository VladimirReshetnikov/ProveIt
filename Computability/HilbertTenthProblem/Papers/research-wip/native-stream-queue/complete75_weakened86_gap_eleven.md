# A fixed-gap finite reduction and exclusion of gap eleven

Every positive zero of the [unchanged86 candidate](complete75_weakened_bound86_candidate.md)
with **R<0 and mu>0** satisfies

    p odd, n<p<=2n-13.

The [gap-nine theorem](complete75_weakened86_gap_nine.md) left the equality
p=2n-11. This packet excludes it using1,413 exact ratio-domain certificates.
It also proves a reusable theorem: **for each fixed odd gap g=2n-p>=3,
the full positive-input branch has an effectively computable finite set
of possible(q,p,w,Y)**. The theorem does not bound g, and does not claim
that every finite set is empty.

The [source](complete75_weakened86_gap_eleven.py) and
[receipt](complete75_weakened86_gap_eleven.json) retain every gate and
hypothesis of the86=48M+38A candidate, its19 positive coordinates and
exact degree203. Gaps at least13 and mu<0 remain unresolved. No complete
false-input zero or universal86 theorem is claimed. The separate75/87
bounds remain unchanged.

## 1. Full-source hypotheses and a uniform packing inequality

Assume a complete positive candidate zero with R<0,mu>0. The
[index-gap theorem](complete75_weakened86_index_gap.md) and the gap-nine
packet supply the actual compiler and Pell conditions

    B=2^d, d>=4, J>=1, q=(B-1)J+1>=16,
    X=wq^3, Y=sq^3, w,s>=1,
    a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    P=2XY^2+1, k=2*psi_P(n), c=psi_A(p),
    kY<c<k(Y+1), p odd>=13, n<p<2n.

Here A is the mathematical Pell parameter; the literal source register
named A holds Delta. In particular the full normalized strong equation,
both ratios and the recovered rank/index conditions are retained.
Let g=2n-p be a fixed odd integer at least3. Then p>g and n=(p+g)/2.
With b_p=psi_2(p) and M=q^2-1, the inherited bounds are

    Y<=U=(2q^2-3)b_p+3p-1,
    U+1<=2q^2*b_p,
    (X+1)^((p-g)/2)<2^g*Y^(g-1)*(Y+1),             (1)
    X=2^p modulo H, 0<X<H, X<=2^p.                 (2)

The positive input root has an index0<v<p and satisfies

    kappa=psi_A(v), mu=chi_A(v),
    kappa=u+delta*Delta, u=2d*x+b, 0<b<B,
    C=q-F-alpha-2d*x>=0, C<q,
    W=C-Z=E_A(v)-rho*H,
    E_A(t)=chi_A(t)-(A-2)psi_A(t).                  (3)

All supplied x,F,alpha,delta,rho are positive. The fixed offset b is
distinct from b_p. Write the two fixed positive masks as M_C,M_F and set

    Tmask=(M_C+q*(M_F+B-1))*J>0,
    K=q(q-F)M+Tmask, 0<K<q^4,
    R=K-MZ,
    R+epsilon-lambda=omega*p-j*c,
    epsilon,lambda,omega in{1,-1}, 0<=j<=2q^2-3.   (4)

The j in(4) is a wrap count, not the supplied auxiliary with that name.
A useful strengthening of the earlier small-q argument is the exact identity

    K-MC=M*((q-1)C+q*(alpha+2d*x))+Tmask>0.         (5)

Here MC means the product M*C, not the mask M_C. Thus positivity of
K-MC does not require2^(2d+1)>q. This distinction matters for arbitrary
fixed gaps, where the finite low-X scales can be much larger than in
the preceding packets.

## 2. Every fixed gap has finitely many power-X cases and low-X lanes

If X<2^p, equation(2) gives H<=2^p-X<2^p and therefore
Y<2^(p-2)/(X+1). Substitute into(1), using Y+1<2Y:

    (X+1)^((p+g)/2)<2^(gp-g+1).                    (6)

If X+1>=2^(2g), the left side is at least2^(gp+g^2), contradicting(6).
Consequently

    X=2^p; or X+1<2^(2g).                          (7)

In the power branch q=2^t,4<=t<=floor(p/3),w=2^(p-3t).
Using U+1<=2q^2*b_p and b_p<=4^(p-1), equation(1) implies

    2^(p(p-g)/2)<2^(2g)*q^(2g)*b_p^g<=2^(8gp/3),
    hence 3p<19g.                                 (8)

There are only finitely many possible(p,t), and thus(q,p,w).
In the other branch wq^3<=2^(2g)-2. Since B<=q and
q=(B-1)J+1, finitely many actual(d,J,w) occur. The executable enumeration
uses only these exact compiler relations; it does not replace them by
arbitrary small Pell parameters.

## 3. A uniform index cutoff in every low-X lane

Fix g and one low-X lane(d,J,w), hence fixed B,q,X. Equation(3) gives

    u_min=2d+1<=u<=u_max,
    u_max=2d*floor((q-2)/(2d))+B-1.                 (9)

Define exact integers

    T=q^4+M*2^u_max+2,
    A0=3X*T+2(2q^2-3)(X^2-1), A1=3X,
    h=floor(log_2(X+1))>=12,
    e(p)=floor((h(p-g)-2(g+1))/(2g)).               (10)

The logarithm notation is computed by integer bit length. Equation(1)
and Y+1<2Y give

    Y^g>(X+1)^((p-g)/2)/2^(g+1), hence Y>2^e(p).   (11)

When h>=g, e(p+2)>=e(p)+1. Choose the first odd p0>=max(13,g+2)
with

    2^e(p0)>max(A0+A1*p0,p0,u_max).                (12)

Doubling the three bounds proves(12) for all odd p>=p0; the linear
inequalities are checked at p0 and become stronger as p increases.

For arbitrary g, including h<g, use instead the exact identity

    e(p+2g)=e(p)+h.                                (13)

Choose the first odd p0>=max(13,g+2) for which

    2^e(p0)>max(A0+A1*(p0+2g-2),p0+2g-2,u_max).    (14)

Monotonicity of e proves the required starting bound on each of the g
odd indices from p0 through p0+2g-2. Multiplying by2^h preserves all
three bounds under p->p+2g: indeed h>=12 and p>g imply
2^h*p>p+2g and2^h*(A0+A1*p)>A0+A1*(p+2g).
Thus induction on each odd residue class modulo2g proves the result
for every odd p>=p0. Both cutoff searches terminate because(13) gives
geometric growth while their thresholds grow linearly. This is an
all-index proof; finite envelope replays only supplement it.

In either case, equations(11)--(14) give

    H>Y>max(A0+A1*p,p,u_max)                        (15)

for every odd p>=p0. We next prove that(15) is impossible at a full zero.

Since0<v<p<Y<A and u<=u_max<Y<A, the exact discriminant congruence

    psi_A(v)=v modulo Delta if v is odd,
    psi_A(v)=v*A modulo Delta if v is even

has its displayed representative in(0,Delta). The even representative
is at least2A>u. Equation(3) therefore forces v=u odd. The inherited
identity E_A(u)=2^u modulo H gives Z=C-2^u modulo H. Set

    Theta=K-MC+M*2^u+epsilon-lambda.

Equation(5), M>=255 and u>=9 prove Theta>0; K<q^4,C>=0 and(9) give
Theta<T. The wrap in(4) implies Theta=omega*p-jc modulo H.
The actual main norm gives, without dividing by3,

    3Xc=2(X^2-1) modulo H.

Consequently H divides

    L=3X*(Theta-omega*p)+2j*(X^2-1).               (16)

But(10),(15) give |L|<A0+A1*p<H, so L=0. Reduction modulo X implies
X divides2j. Since0<=2j<=4q^2-6<q^3<=X, j=0. Then Theta=omega*p;
positivity forces omega=1. The original wrap gives R>=p-2>0,
contradicting the chosen branch. Hence every low-X zero has p<p0.

Combining the finite lanes, their finite indices and Y<=U proves the
stated effective finite reduction for each fixed odd gap. The theorem
does not assert an index cutoff independent of g or exclude all gaps.

## 4. The exact gap-eleven domain

For g=11, the power branch has odd13<=p<=69. It contains300 triples
(q,p,w). The low branch has X<=2^22-2, hence q<=161 and4<=d<=7.
The actual compiler relation gives the following1,414 lanes. Here each
allowed w is a separate lane; p0 is its exact cutoff from(12).

| q | Number of lanes | Range of p0 | Remaining(q,p,w) triples |
|---:|---:|---:|---:|
|16|1023|69--97|161|
|31|140|89--117|374|
|32|127|111--143|87|
|46|43|107--131|112|
|61|18|125--147|103|
|63|16|145--173|146|
|64|15|179--203|24|
|76|9|141--159|24|
|91|5|159--173|39|
|94|5|177--193|31|
|106|3|177--183|6|
|121|2|185--193|0|
|125|2|211--219|0|
|127|2|245--255|6|
|128|1|317|0|
|136|1|203|0|
|151|1|219|0|
|156|1|243|0|

For this gap h>=12>11, so the simpler two-step induction applies.
The receipt lists every lane and its exact constants and cutoff.
For odd13<=p<p0, retain X<2^p and write X=2^ell*o with o odd.
Since H is odd, equation(2) gives

    H divides N=2^(p-ell)-o>0,
    N>=4q^3(X+1)+3.                                (17)

It also gives Y<2^(p-ell-2)/(X+1); substituting into(1) yields

    (X+1)^((p+11)/2)<2^(11(p-ell)-10).             (18)

Exact integer tests(17),(18) leave the1,113 low-X triples in the last
column. Together with the300 power triples, there are1,413 ratio domains.
The receipt contains the entire finite list; none is called a candidate zero.

## 5. Every remaining scale fails a strict ratio

For each listed(q,p,w), set n=(p+11)/2 and X=wq^3. Define

    F(Y)=2Y*psi_(1+2XY^2)(n)-psi_(2+(X+1)Y)(p),
    G(Y)=2(Y+1)*psi_(1+2XY^2)(n)-psi_(2+(X+1)Y)(p).

The retained ratios require F<0<G at Y=sq^3,1<=s<=floor(U/q^3).
For every listed triple the exact coefficient arrays have degree p+10,
strictly negative coefficients below degree p, nonnegative coefficients
at or above p, and positive leading coefficient. Therefore both
F(Y)/Y^p and G(Y)/Y^p are strictly increasing on Y>0.

The checker first tests s=1. Otherwise geometric bracketing and exact
binary search locate the last allowed s with F<0. If none exists,
F(1)>=0 excludes every scale. If a last scale exists, G there is
nonpositive in every domain, excluding all earlier scales as well.
The adjacent endpoint has F>=0 when it lies within the scale bound.
Every recorded boundary is checked again by independent evaluation
of the exact coefficient arrays with Horner's rule.

All1,413 domains fail. There are2,826 per-domain coefficient-sign
certificates and2,276 distinct arrays. Unlike gap nine, no ratio survivor
needs a subsequent wrap test. Thus p=2n-11 is impossible. The preceding
theorem already made the gap an odd integer at least11; it is now at
least13, proving n<p<=2n-13 on R<0,mu>0.

## 6. Source checks and scope of the evidence

The writer passes with158,624 exact Pell evaluations and2,720 Horner
endpoint checks. A separate author search using binary search from the
full upper bound agrees on every last lower-ratio scale; the final source
uses geometric bracketing. This is a second search schedule using the
same Pell/array helpers, not an independent proof review.

The checker imports the unchanged complete86 source hash and all guarded
strong/input rows through the gap-nine source contract. The new uniform
positivity audit verifies the exact packing identity(5), including scales
where2^u_min<=q. Its positive masks in those isolated tests need not obey
the full compiler's population condition, and the tests claim only the
algebraic identity and positivity under their stated assumptions.

There are1,920 packing positivity checks, including96 packing tuples
whose q exceeds the old input-index lower power. These do not assert the
existence of a complete candidate zero.

The general-cutoff fixtures additionally include gaps13,21,51,101 and
lanes with h<g. Every odd residue class required by the larger induction
step is checked at its initial window and later exact indices, for6,320
exact induction-envelope checks in total. The proof
in Section3 supplies the infinite conclusion. The retained individual
Pell input-classification checks and signed main/wrap correction identities
are replayed from the preceding packet; these are component/algebraic
audits, not constructed complete positive native extensions.

Reproduce the exact source/receipt checks with:

```sh
python3 complete75_weakened86_gap_eleven.py
```

The first writer and fresh author default replay pass; all five local
links resolve. An independent full proof/source/fresh-default review passes,
with no findings. Its separate polynomial recurrence regenerated all2,276
coefficient arrays and checked the sign conditions, verified all2,720
Pell/Horner endpoints, and independently enumerated every one of1,414
compiler lanes, cutoffs and remaining-index lists. Root full proof/source
review and fresh default replay also pass with no findings. Its independent
lane audit enumerated all1,414 actual compiler lanes, found their minimum
odd cutoffs by doubling and binary search rather than the author’s linear
scan, and checked every finite-index list and the300 power/1,113 low
domain split. The general growth bounds, true packing identity, all-residue
induction for h<g, input classification and final residue contradiction
were reviewed independently.
No frozen parent,
candidate arithmetic or navigation file is edited by this packet.
