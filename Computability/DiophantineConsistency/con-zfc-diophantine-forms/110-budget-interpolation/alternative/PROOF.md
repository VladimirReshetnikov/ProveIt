# Power fusion for a global tiling certificate

## Result and exact limits

This note proves a chain of improvements to the previously supplied global Wang-tiling certificate. They apply to **every fixed finite strict-boundary tile set**, not just K215 and not just square boards.

* Five exposed natural coordinates, **one** fixed-base-2 graph and one total-binomial graph, instead of six coordinates and two power graphs for arbitrary rectangles.
* Seven exposed natural coordinates and **three** power graphs, two fixed-base-2 and one general-base.
* An alternative with eight exposed natural coordinates and **two** power graphs, one fixed-base-2 and one general-base.

These are exact arithmetic interfaces, **not** ordinary polynomials in five, seven or eight variables. If fixed-base exponentiation requires p2 internal natural witnesses, general exponentiation requires pg, and total binomial requires b, the respective ordinary-polynomial variable counts are **5+p2+b**, **7+2p2+pg**, and **8+p2+pg**. All internal witnesses must actually be compiled before any numerical ordinary-polynomial count is asserted. No direct ZFC proof-checker tile set or complete internal ZFC interpretation is supplied here.

The advance is a proved elimination of special-function calls and exposed coordinates. It does not beat the project's nine-positive, twelve/thirteen-integer or low-degree ordinary-polynomial frontiers by itself. It does not claim historical priority for power synchronization or positional arithmetization.

## 1. Fixed coefficients and the ordinary polynomial circuit

Let k>=1 tiles have natural edge colors (w_t,e_t,n_t,s_t); color zero occurs exactly at the outer boundary. Choose C=2^c greater than k and all colors. Put A0=4C^2 and choose D a power of two with D>=32kA0. These are fixed integer coefficients.

For now use natural coordinates a,Q,G,Z,r and require

    P = 1+(C-1)G = 2^(c(a+1)).                         (G1)

In particular P>=C, G>=1. Define ordinary polynomials

    H=A0 P,   R=D P^3,   B=(D/2)P^3,   L=R^(2k).

All powers in the circuit below have fixed integer exponents. The expression L/(2P) is only an abbreviation for the ordinary polynomial

    (D^(2k)/2) P^(6k-1).

For a formal vector x=(x_0,...,x_(k-1)), let U=sum_t x_t and use these seven linear residuals ell_j(x)=sum_t a_jt x_t+c_j:

1. U-G.
2. (Q-1) sum_(w_t=0) x_t -(P-1).
3. Q sum_(w_t=0) x_t - C sum_(e_t=0) x_t.
4. C sum_t e_t x_t - sum_t w_t x_t.
5. Q sum_t s_t x_t - sum_t n_t x_t.
6. Q-1 -(C-1) sum_(n_t=0) x_t.
7. Q sum_(s_t=0) x_t - P sum_(n_t=0) x_t.

The vector x is **not** a tuple of certificate variables: it is recovered as the base-R digits of Z in the proof. Rows 3 and 6 have been reversed relative to the previous certificate. This is essential to the nonnegative bootstrap when Q is initially unbounded.

Define

    K_j = sum_(t=0)^(k-1) (H+a_jt) R^(k-1-t),
    F_j = K_j Z + (B-HG+c_j) R^(k-1),
    T_7 = F_7 + Q L/(2P),
    M0 = G sum_(t=0)^(k-1) R^t,
    M1 = R^(2k-1)-1 -(R-1-B) R^(k-1),
    Mtop = L-1 -(R-1-B) R^(k-1),
    A = M0 + M1 sum_(j=1)^6 L^j + Mtop L^7,
    Y = Z + sum_(j=1)^6 F_j L^j + T_7 L^7.

The old highest convolution lane had an unused top base-R digit. Mtop opens this digit and Q L/(2P) uses it as a bound certificate, without adding a variable or another packed lane.

Finally require the one total-binomial graph

    binom(A,Y)=2r+1,                                  (G2)

with binom(A,Y)=0 when Y>A.

**Theorem 1.** There are natural a,Q,G,Z,r satisfying (G1),(G2) if and only if the fixed tile set has a finite strict-boundary rectangular tiling.

## 2. Bootstrap without assuming Q is a geometric power

For natural Q, every coefficient H+a_jt is at least H-P-C and in fact at least H-max(P,C,1)>0. To check the only potentially unbounded terms, observe that Q occurs with nonnegative coefficients in rows 2, 3, 5 and 7. In row 6 it occurs in the constant term Q-1. The smallest possible constants c_j are greater than or equal to -P. Thus every offset

    B-HG+c_j >= B-HP-P > 0.

Consequently every F_j is nonnegative and F_7>=Z, for every natural Q,Z, before any range assertion on Q.

Under (G1), R is a power of two. Also M0<L, M1<L and Mtop<L, so A<L^8. Binary Lucas parity says (G2) is equivalent to every 1-bit of Y being a 1-bit of A, hence Y<=A<L^8. Nonnegativity then implies

    F_7 + Q L/(2P) = T_7 < L.

It follows simultaneously that

    Z<L,             Q<2P.                           (B)

Now the bottom L-block of Y is exactly Z. Therefore Z is a binary subset of M0. Write

    Z=sum_(t=0)^(k-1) x_t R^t.

Each x_t is a binary subset of G and 0<=x_t<=G<P. No higher base-R digit occurs. This derivation does not assume Q|P, the existence of rectangle dimensions, or any unproved absence of carries.

## 3. No-carry proof and the seven exact linear identities

Once (B) is established, every |a_jt|<=H/2 and every |c_j|<=2P. All noncentral coefficients of the formal convolution F_j are bounded by

    2kHG < 2kA0 P^2 < R/8.

The central coefficient at position k-1 is

    d_j=B+ell_j(x)+H(U-G).

The nonnegative convolution description gives

    B-HG-2P <= d_j <= B+2kHG+2P.

The choice D>=32kA0 and P>=2 makes the lower bound positive and the upper bound less than R. For example, 2kHG<R/32 and 2P<R/32 already suffice. Hence there are no carries in any F_j, and F_j<R^(2k-1).

Moreover

    Q L/(2P) = (Q R/(2P)) R^(2k-1),

where Q R/(2P) is an integer less than R by (B). Thus adding the guard to F_7 changes only its previously unused highest digit. In particular T_7<L, and its central digit remains d_7.

All eight L-lanes now separate. The masks M1 and Mtop allow only the single bit B at each central position. Since every d_j>0, their binary-subset tests force d_j=B. The first row yields

    (H+1)(U-G)=0,

so U=G. Every remaining central equality is then ell_j(x)=0.

Conversely, if x_t are binary subsets of G and the seven linear residuals vanish for a genuine rectangle, Q<=P. We have F_j<R^(2k-1), and the guard is at most L/2, so T_7<L. Its high digit is unrestricted by Mtop, and all central digits equal B. Thus Y is a binary subset of A, proving the converse packed test.

## 4. Recovering the whole geometry from boundary equations

Write P=C^N, where N=a+1>=1. The digit mask G=1+C+...+C^(N-1) gives x_t base-C digits in {0,1}. Since k<C, the identity U=G says exactly one tile occupies each of the N cells, without carry.

Let W0,N0,S0 denote the sums of tile masks with west, north, and south color zero. Rows 2 and 6 give

    (Q-1)W0=P-1>0,
    (C-1)N0=Q-1.

The second identity forces Q>=1, and the first excludes Q=1, so Q>=2. The second also gives gcd(Q,N0)=1. Row 7 gives Q S0=P N0, hence **Q divides P**. Since P is a power of two, Q=2^u for some u>=1. The divisibility C-1|Q-1 implies c|u, so Q=C^w with w>=1. Finally Q-1|P-1 implies w|N. Put h=N/w>=1: then P=Q^h.

The elementary fact used twice is

    b^s-1 divides b^t-1  iff  s divides t    (b>=2,s,t>=1).

For the reverse implication, write t=qs+r, 0<=r<s; reduction modulo b^s-1 yields b^r-1, which is zero only for r=0.

Now the boundary masks have their exact meanings:

    W0=(P-1)/(Q-1),          E0=(Q/C)W0,
    N0=(Q-1)/(C-1),          S0=(P/Q)N0.

They are the first column, last column, first row and last row of a width-w, height-h rectangle. Rows 4 and 5 check horizontal and vertical edge equality. At row joins the colors are zero, exactly as imposed by the boundary masks. Thus the recovered board is a strict-boundary tiling. Conversely every such tiling gives N=wh, a=N-1 and the indicated Q,G,Z, proving Theorem 1.

This proof works for arbitrary rectangular tile sets. No assumption that rectangles can be padded to squares is needed.

## 5. Fusing the geometry into parity extraction: three graphs

For the remaining interfaces, replace G by g+1 and define

    P=C+(C-1)g,

so P>=C without a power-graph index. Keep the entire ordinary circuit of Section 1, now in Q,g,Z.

For arbitrary natural A,Y, if d=2^(A+1), the base-d digits of (d+1)^A are binom(A,i), all strictly less than d. Consequently binom(A,Y) is odd iff

    d=2^(A+1),
    e=2^((A+1)Y),
    (d+1)^A=e(2q+1)+s,
    e=s+t+1

for natural d,q,s,t. This also excludes Y>A, because the corresponding quotient would be zero.

Substitute **d=P v**; do not introduce d as another coordinate. The seven exposed coordinates are

    Q,g,Z,v,q,s,t.

Define e=s+t+1 and impose exactly these three graphs:

    P v = 2^(A+1),
    s+t+1 = 2^((A+1)Y),
    (s+t+1)(2q+1)+s = (P v+1)^A.                     (T3)

Soundness: the first graph makes P a positive power of two. Since C-1|P-1, P is a positive power of C. Sections 2-4 now apply to the parity condition extracted from (T3).

Completeness: a genuine tiling gives odd binom(A,Y), so Y<=A. Also A>=P and A>=10: indeed Mtop has highest base-R digit R-1, and R>=512P^3. Hence A+1>=log_2(P), and 2^(A+1)/P is a positive integer. Set v to this quotient and use the standard parity witnesses. Thus no tiling is lost by d=P v.

**Theorem 2.** The fixed tile set has a strict-boundary rectangle iff (T3) has natural solutions in its seven exposed coordinates.

## 6. Second-order power synchronization

Here is the precise elementary lemma used to remove one more graph.

**Lemma.** Let n,Y,d,e be positive integers, with d>n+1, e=2^n, d|e, and

    e-1=(d-1)(Y+(d-1)j)

for some integer j. If 1<=Y<=n, then e=d^Y.

Proof. Divisibility d|2^n makes d=2^u for some u>=1. The displayed identity implies d-1|e-1, so u|n; write n=uh, e=d^h. Since

    (e-1)/(d-1)=1+d+...+d^(h-1) = h mod (d-1),

we have h=Y mod(d-1). Both h and Y lie in [1,n], and n<d-1, hence h=Y. This proves the claim.

The size hypothesis cannot be discarded: n=3,e=8,d=2,Y=1,j=6 satisfies the divisibility and congruence but 8 is not 2^1.

## 7. The two-graph, eight-coordinate certificate

Keep P=C+(C-1)g and A,Y from Sections 1 and 5. Take eight exposed natural coordinates

    Q,g,Z,v,q,u,t,j.

All of the following are ordinary polynomial definitions:

    n=(A+1)Y,
    d=P(n+v+1),
    e=d(u+t+1),
    W=e(2q+1)+du+1,
    S=e-1-(d-1)(Y+(d-1)j).

Require only

    e=2^n,                    W=(d+1)^A,             (T2)
    S=0.

There are **two** variable-power graphs, not three. The equality S=0 is already an ordinary polynomial constraint. The parametrization e=d(u+t+1) supplies d|e without a new quotient witness: the same u,t also encode the Euclidean remainder du+1.

### Soundness

For every natural Q,g,Z, the pre-bootstrap positivity argument in Section 2 gives Y>=1. Also A>=10 and P>=2, so n>=Y and

    d=P(n+v+1)>=2(n+1)>n+1.

The first graph in (T2), the definition of e, and S=0 satisfy the lemma, so e=d^Y. Because e=2^((A+1)Y) and Y>=1, cancellation of positive integer exponents gives d=2^(A+1).

As P|d, P is a power of two and, from C-1|P-1, a power of C. Moreover

    0<=du+1<d(u+t+1)=e,

because e-(du+1)=d(t+1)-1>=1. Thus the second graph has odd Euclidean quotient 2q+1 upon division by d^Y. Since d=2^(A+1), this says binom(A,Y) is odd. Sections 2-4 recover an actual tiling.

### Completeness and every witness

For an actual tiling take its Q,g,Z and define

    n=(A+1)Y,   d=2^(A+1),   e=d^Y,
    W=(d+1)^A,
    m=floor(W/e),   s=W-em.

Odd binomial parity gives m odd and positive. Also W=1 mod d and e=0 mod d, so s=1 mod d and 1<=s<e. Set

    q=(m-1)/2,
    u=(s-1)/d,
    t=e/d-u-1,
    j=((e-1)/(d-1)-Y)/(d-1),
    v=d/P-n-1.

The first four quantities are nonnegative integers: for j, use the sum 1+d+...+d^(Y-1)>=Y and its congruence Y modulo d-1.

To check the remaining coordinate v, use Y<=A, P<=A and A>=10. For all integers A>=10,

    2^(A+1)>A^3+A^2+A >= P((A+1)Y+1).

The exponential bound holds at A=10 and follows by induction: twice the cubic on the right exceeds its next value for every A>=4. Since d/P is an integer, v=d/P-n-1>=0. Thus every stated witness exists and (T2), S=0 hold.

**Theorem 3.** The fixed tile set has a strict-boundary rectangle iff the two-graph eight-coordinate certificate has a natural solution.

## 8. Exact ordinary-polynomial contracts and degree bounds

Let E2(m,z;eta)=0 be an exact graph for z=2^m on naturals, with p2 internal natural witnesses and total degree delta2. Let Eg(b,m,z;theta)=0 be an exact graph for z=b^m, with pg internal witnesses and degree deltag. Let J(A,Y,z;xi)=0 be an exact graph for total binomial, with b internal witnesses and degree deltaB.

Every occurrence receives its own independent internal witness tuple. The five-coordinate certificate becomes

    E2(c(a+1),P;eta)^2 + J(A,Y,2r+1;xi)^2 = 0.

It has 5+p2+b natural variables. The circuit polynomials A and Y have degree at most 48k in Q,G,Z, so a degree bound is 2 max(delta2,48k deltaB).

The seven-coordinate certificate becomes the sum of squares of the three graph polynomials in (T3), with 7+2p2+pg variables. A degree bound is

    2 max(96k delta2,48k deltag).

The eight-coordinate certificate becomes the literal ordinary polynomial

    E2(n,e;eta)^2 + Eg(d+1,A,W;theta)^2 + S^2 = 0.

It has 8+p2+pg natural variables. Degree bounds for its ports are

    deg A,deg Y <=48k,
    deg n<=96k,  deg d<=96k+1,
    deg e<=96k+2, deg W<=96k+3, deg S<=192k+3.

Hence its degree is at most

    2 max((96k+2)delta2,(96k+3)deltag,192k+3).

These bounds intentionally count graph inputs as polynomial substitutions, not additional variables. A separate flattening for lower degree would introduce more variables and must be counted separately. Translating naturals to unrestricted integers also has additional costs; no integer-variable frontier is asserted here.

## 9. Relation to the consistency problem and validation status

The transformation is tile-set independent. It can be applied unchanged to the previous literal K215 tile set, but it does not depend on that choice. A genuinely independent ZFC-checker tile set, its equivalence to internal proof existence, and the graph polynomials remain separate obligations. The construction therefore closes a specific arithmetic interface gap without claiming to complete the alternative Con(ZFC) polynomial.

`core.py` is an exact integer evaluator of the fixed-power packed circuit. `check.py` compares it to direct tiling verification, including arbitrary invalid Q, malformed masks and oversized packed words. It also checks both synchronization lemmas and the two-graph extraction kernel at manageable sizes. Binary Lucas evaluation is used only for exact parity, and is never labeled an ordinary-polynomial implementation. `build_dag.py` emits a fixed-power integer-polynomial DAG and verifies it against the separate direct evaluator. Ordinary exponentiation graph polynomials are deliberately not fabricated.

The universal proofs above, not finite tests, establish the theorems. No Lean/Isabelle kernel check is claimed. See SOURCES.md for primary background and the exact predecessor files.
