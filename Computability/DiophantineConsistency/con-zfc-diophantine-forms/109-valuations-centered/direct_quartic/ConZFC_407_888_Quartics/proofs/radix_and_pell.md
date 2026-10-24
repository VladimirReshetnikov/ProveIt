# Additive Pell indices and a recycled factorial radix

These are two separate existence-preserving transformations of the direct
nonnegative-integer proof-certificate equation. Both use ordinary polynomial
identities. Variable exponentiation below denotes the mathematical relation
already represented by the shared finite Pell graph; it is not an operation
left in the exported polynomial.

## 1. Precise assumptions for radix recycling

Let R,t,H be positive integers satisfying

* R >= 4, 1 <= t <= R, H >= R^4;
* the number r of range columns satisfies 1 <= r <= H;
* every range lower index k satisfies 1 <= k <= R.

The released projected source has r=8, R=2+t+x+y+M0, and
H=R^8388608. Since t>=1, R>=3 (and in fact the endpoint and carrier
rows force R>=4). Thus H>=256>=8, t+2<=H and R(R+2)<=H.
The earlier eleven-column source used R=2+t+x+y+m+M0 and m=t;
it satisfies the same stated assumptions. No estimate uses r=11 specially.

Put rho_n=(n+2)^(n+2), V_n=(rho_n+1)^n, and V=V_H. The two
factorial graphs in the construction already request the powers rho_H,V_H
and rho_t,V_t. Let T denote the proposed output of the H-factorial graph.
Let Q=(1+(t+1)T)^t+2, and let B be the proposed CRT product, represented as
a remainder modulo TQ-1. Independently of the correctness of that product
formula, its division rows imply 0 <= B < TQ. Its other division inputs
are those of the unchanged CRT product formula.

The r encoded row coordinates a_i are positive. Add just one natural
variable g and the quadratic (indeed affine) row

    sum_i a_i + g = r B.                              (A)

Use the common radix

    q = B(V+1)                                       (B)

in every binomial digit graph. No new power is needed for this definition.
The exact binomial graphs are precisely

    C(rho_H+H,H), C(rho_t+t,t), C(Q+t,t).

The r remaining requests only require B | C(a_i,k_i).

## 2. The low-digit extraction lemma

For n,k >= 0 let c_j=C(n,j), with c_j=0 for j>n. If q>=2 and
0<=c_j<q for every 0<=j<=k, then

    floor((q+1)^n/q^k) mod q = C(n,k).               (C)

Indeed the binomial expansion has lower part sum_{j<k} c_j q^j < q^k,
coefficient c_k at q^k, and a higher part divisible by q^(k+1).
There is no condition on coefficients above k. This weaker radix condition
is what makes recycling possible.

For the fused divisibility graph, suppose B>=1, B|q and the same low-digit
bound holds. Write the ordinary quotient h0=floor((q+1)^n/q^k). Then
h0=C(n,k)+q h1 for an integer h1>=0. Consequently

    B|h0 iff B|C(n,k).

The rows

    (q+1)^n = q^k B h + u,
    q^k = u+s+1

with natural h,u,s therefore express exactly B|C(n,k). There is no need
to retain the digit itself, its high-digit quotient, or its digit-bound
slack.

## 3. Soundness order: no circular use of the CRT product

First apply the independently proved shared-power theorem to all power
requests simultaneously. All exponent atoms are positive by their source
construction. For a proposed power base n, its modulus row is

    2 A n = T_n + n^2 + 1,

where T_n is natural. This excludes n=0, so in particular the radix q
is positive without assuming that B is already the true CRT product.
Equation (B) then implies B>=1 and hence q>=V+1>=2.
The simultaneous theorem supplies the exact numerical values rho_H,V_H,
rho_t,V_t,Q and every power in the binomial digit graphs. Dependencies
between their proposed inputs do not invalidate this pointwise theorem.

Second, recover T=H! before using any estimate involving H!. Since
rho_n>=n and j<=n, binomial unimodality gives

    C(rho_n+n,j) <= C(rho_n+n,n) <= (rho_n+1)^n.      (D)

The last inequality follows either by injecting weakly increasing words
of length n over rho_n+1 letters into all such words, or from
C(rho_n+n,n)=prod_{i=1}^n (1+rho_n/i). Thus the H-factorial binomial's
low coefficients are at most V<q. Its exact digit graph is correct;
the inherited factorial identity now implies T=H!. Also H>=t, so
V_t<=V, and the same argument recovers the t-factorial output t!.

Third, establish all remaining low-digit bounds using only the RAW
remainder inequality B<TQ, not the unproved identity for B. Since
T=H!<=H^H and t+2<=H,

    1+(t+1)T <= (t+2)T <= H^(H+1).

Let e=t(H+1)>=1. Then

    Q+t <= H^e+t+2 <= H^e+H <= H^(e+1).

In particular Q<=H^(e+1). By (A), a_i<=rB<rTQ; because r<=H,

    a_i < rTQ <= H^(H+e+2) <= H^((t+2)(H+1)).       (E)

The same last bound holds for Q+t. If n is any one of these remaining
upper arguments and 1<=k<=R is its lower index, then n>=1 and

    C(n,j) <= n^j <= n^k
             <= H^(k(t+2)(H+1))
             <= H^(H(H+1))                         (0<=j<=k),

using k(t+2)<=R(R+2)<=H. On the other hand,

    V=(rho_H+1)^H > (H+2)^(H(H+2)) > H^(H(H+1)).    (F)

All remaining low-digit coefficients are therefore <V<q. Now the
CRT-product binomial and each fused range divisibility graph are exact.
Only at this stage is the inherited product formula invoked to identify
B with prod_{i<t}(1+(i+1)T). The usual fixed-coordinate CRT decoding and
direct proof-certificate argument can then proceed unchanged.

This order is essential. Proving (E) from the final CRT product identity
before validating its binomial would be circular. The raw remainder bound
is sufficient and is already a literal consequence of the emitted rows.

## 4. Completeness and the aggregate representative bound

Given a valid finite proof certificate, choose the existing outer bounds,
trace code and H as in the inherited construction. Set T=H! and set B
to the true positive CRT product. Every CRT solution for a column has a
positive representative in the interval [1,B]: take its least nonnegative
representative, replacing zero by B. These changes preserve every modular
condition. Hence sum_i a_i<=rB, and the natural value
g=rB-sum_i a_i satisfies (A).

Set q=B(V_H+1). The estimates above prove all needed binomial extractions,
so ordinary Euclidean quotients and remainders satisfy the exact and fused
rows. Finally choose the shared Pell frame and its finitely many auxiliary
witnesses as in the inherited completeness theorem. This proves existence
preservation in both directions; it does not claim a bijection between
all old and new raw certificates.

## 5. Deriving Pell indices by addition

For a common natural A>=2 put D=A^2-1. Define

    X_0=1, Y_0=0,
    X_1=A, Y_1=1,
    X_{n+1}=A X_n + D Y_n,
    Y_{n+1}=X_n + A Y_n.

Multiplication in the rank-two ring Z[s]/(s^2-D), or elementary induction,
gives the exact identities

    X_{u+v}=X_u X_v+D Y_u Y_v,
    Y_{u+v}=X_u Y_v+Y_u X_v.                        (G)

In particular (X_2,Y_2)=(2D+1,2A). Introduce D as a natural variable
with A^2=D+1. All right-hand sides in (G), including the fixed-index pairs
for 1 and 2, are polynomials with nonnegative coefficients in their
stored coordinates. They therefore give total and unique natural-valued
restorations; no sign selection or Pell-root ambiguity remains.

The compiler first records all required positive power exponents. It emits
a full shared Pell-index test only for seed exponents. If an exponent
node is a sum of two other requested exponents, or the sum of a requested
exponent and the literal constant 1 or 2, its pair is instead constructed
by (G). Every dependency points to an earlier source-arithmetic addition
node. Thus the graph is acyclic; induction in that order proves that every
derived pair is the intended indexed Pell pair.

Only the seed indices enter the auxiliary product of Y_i^2. The common
auxiliary Pell solution, its period construction, and its third-norm tests
are needed solely to recover those seeds. Derived pairs require no extra
auxiliary congruences. Once their exact index is recovered algebraically,
the unchanged power-congruence proof applies to them.

For completeness, construct the seed indexed Pell pairs and the inherited
common auxiliary witnesses for that finite seed set. Evaluate (G) for all
derived nodes. This supplies every deleted index test's semantic role.
For soundness, recover the seed indices from their unchanged tests, then
apply the acyclic induction. All statements are elementary finite integer
arithmetic and finite CRT/Pell arguments, and may be formalized in ZFC.

## 6. Concrete audit boundary

The exported JSON is an ordinary sum of squares of listed quadratic rows.
The added discriminant, aggregate bound and index-addition identities are
all explicit polynomial rows or nonnegative arithmetic gates. Their
novel algebraic identities and dependency order are checked independently
from a saved raw-row ledger; the monic contraction is independently replayed.
Finite arithmetic fixtures test transcription of low-digit extraction and
Pell addition. Those fixtures are not substituted for the unbounded proofs
in Sections 1-5, and none of this proves Con(ZFC) itself.

## 7. Projected-carrier degree bootstrap

Let all labels lie in [0,h], h>=1, and let there be t rule instances.
Set A(X)=prod_i(1+v_i X) and
C(X)=(1+X)prod_i(1+p_i X)(1+q_i X). Suppose M>1,
M>=(h+1)^t, and A(M)=C(M). Then

    A(M)<(h+1)^t M^t<=M^(t+1).

If deg C>t, its nonnegative leading coefficient is at least one and
C(M)>=M^(t+1), contradiction. Hence deg C<=t. It has at most t
nonconstant linear factors, counting its initial target factor 1+X;
all their labels lie in [1,h]. Thus A(1),C(1)<=(h+1)^t<=M.
Their constant coefficients are exactly one, so every individual
coefficient is <M. Their equal evaluations therefore give A=C by base-M
uniqueness, or by reducing the least nonzero coefficient of A-C modulo M.
This avoids imposing the unnecessary sufficient bound
M>2(h+1)^(2t). The projected carrier ((t+1)^t)^C is valid whenever
h+1<=(t+1)^C, exactly as the explicit label-majorant certificate proves.
