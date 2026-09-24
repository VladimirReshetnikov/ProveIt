# A positive 27-operation Life wrapper derives its own field bounds

The one-field Life construction admits a **27=15M+12A** wrapper whose
positive equations force all three field bounds before the Pell and mask
arguments. With the retained fixed-minus43 kernel, the complete component
has **70=40M+30A operations, 23 positive supplied coordinates, and 12
equations**. Its arithmetic proves the radix power as well as the bounds.

This is a local/mask/kernel component, not a complete Life torus or universal
certificate. The meaning of the inclusive neighbor sum and Boolean typing
of the target remain external obligations. All seven outer coordinates are
strictly positive; zero-plane adapters are not hidden in the count. The
earlier conditional26 source is unchanged.

The [checker](../verification/explore_life_positive_bootstrap.py) and its
[receipt](../verification/explore_life_positive_bootstrap.json) include both
the 27-operation wrapper and all twelve sources of the combined70 ledger.

## 1. The exact local field and the new packing

Use the independently checked scalar relation from
[the one-field Life note](EXPLORATION_LIFE_ONE_FIELD_MASK.md). For
0<=n<=8 and Boolean b,y,u, with s=n+b, put

    v=14s+b+8y+59u+20.

There is exactly one pair (y,u) with v AND72=0 for each n,b, and its y
is the Life output. All 72 possible v lie in [20,214]. Thus

    v'=2v+1=28s+2b+16y+118u+41

lies in [41,429], and v' AND144=0 is the same local condition. We use
radix512 for this field. For whole words define

    V=28S+2B+16Y+118U+41J,
    P=2B+qU+q^2 V,
    M=J(509+510q+144q^2),
    Lambda=q^3, D0=q^5.                                      (1)

The low field of P is 2B, the middle field is U, and V is highest.
This ordering is deliberate: all coefficients of V are positive, and its
coefficient2B is already computed by the nine-operation local schedule.

The **supplied** outer coordinates are the seven positive integers

    S,B,Y,U,J,q,r.

The two outer equations are

    511J=q-1,
    r=(Lambda-P)(Lambda-1)+M.                               (2)

In particular r is not an unrestricted signed output register. Its strict
positivity is an input-domain requirement enforced by supplying positive r
and comparing it with the computed right side for free.

## 2. Positivity forces the raw field bounds

Everything in this section is ordinary integer arithmetic; no radix-power
conclusion, Boolean decoding, Life rule, or kernel soundness is used.

The first equation gives q>=512. Since J>0, M>0, and multiplication of
its definition by511 gives

    511M=144q^3+366q^2-q-509.                               (3)

The difference between511q^3 and the right side is
367q^3-366q^2+q+509>0. Hence M<q^3=Lambda.

If P>=Lambda+1, then the second equation would give

    r<=-(Lambda-1)+M<=0,

contradicting positive r. Thus initially we have only P<=Lambda;
P=Lambda by itself would give positive r=M and must not be dismissed.

However, the positive lower fields in (1) give

    q^2 V<P<=q^3,

so V<q. The positive coefficients in V now yield

    0<2B<V<q,  0<118U<V<q,
    0<28S<V<q, 0<16Y<V<q.                                 (4)

In particular all three raw fields 2B,U,V are integers in [0,q).
Their concatenation therefore satisfies P<q^3: explicitly its maximum
under these three bounds is (q-1)(1+q+q^2)=q^3-1. This excludes the
boundary P=Lambda without presupposing Booleanity.

The arithmetic has also bounded S and Y, but this is not a proof of
Boolean digits for Y or of the required neighbor-count digits for S.
Those semantic obligations remain separate.

## 3. A nonsquare scale is legitimate before power decoding

The exact bounds above imply

    q^3-1<r<q^6,
    q^5<r^2.                                               (5)

For the lower bound use Lambda-P>=1 and M>0. For the upper bound use
r<=Lambda(Lambda-1)+M<Lambda^2. Since r is integral, r>=q^3,
which also proves the second inequality.

Apply the retained base-two kernel at the scale D0=q^5. A square scale
is not an arithmetic premise: the only uses of that supplied expression
are the products X=w D0 and Z=s_p D0. Section6 of
[the general-radix mask note](EXPLORATION_GENERAL_RADIX_BOOLEAN_MASK.md)
audits this issue for the same kernel. Here take n0=q^2 as proof notation;
the corresponding inequalities are

    n0>=64, n0<r<n0^3,
    D0=q^5>n0^2,
    X,Z>=D0,
    E=XZ>=q^10>r+1,
    a=Z(X+1)>q^10>2r+1,
    4r/a<4/q^4<1/2.                                      (6)

These are the bounds actually used by the kernel, rather than an equality
D0=n0^2. The first Pell norm and index congruence give an index at least
r+1; comparison with the main norm gives its index p>=r+2>=66,
c>A_p Delta^2 and c>2r+1. The relaxed auxiliary-rank and normalized-root
arguments recover p=2r+1. They do not use a square root of D0.

The retained ratio argument then gives Z>=X^r and a>X^(r+1). For the
first exponential criterion its explicit growth bounds hold:

    2^(3(2r+1))=8*64^r<X^(r+1)<a,
    X^3<=X^r<a,

because X>=q^5>=4096 and r>=64. The first exponential congruence
therefore gives X=2^(2r+1). The binomial rounding step gives
Z=binom(2r,r) modulo X. Since D0 divides both X and Z, its conclusion is

    q is a power of two,
    D0 divides binom(2r,r).                                 (7)

This is precisely the proof order in
[the base-two Pell proof](BASE_TWO_PELL_90_PROOF.md), with the explicit
nonsquare audit of the general-radix note. No step substitutes n0^2 for
D0. The fixed-minus auxiliary equations have the same soundness proof;
parity is needed only for their positive converse.

Write q=2^e. The paid equation511J=q-1 now forces9|e: reducing e modulo9
would otherwise give a positive remainder d<9 with511 dividing2^d-1,
which is impossible since0<2^d-1<511. Therefore

    q=512^t, t>=1, J=1+512+...+512^(t-1).                    (8)

This establishes field alignment after the raw bounds and before the mask
interpretation.

## 4. Exact extraction and the local semantic interface

With (8), M consists of three t-cell mask words. Digit509=511-2 permits
only a digit0 or2 in the low field2B; digit510=511-1 permits only0 or1
in U; digit144 tests the two forbidden bits of V. Thus the mask condition
P AND M=0 types B,U and imposes the local test on V.

The raw bounds (4) justify this extraction even though B,U were untyped
before the kernel. In particular a whole word2B with only digits0 or2
is twice the corresponding Boolean word, so division by2 recovers B
exactly, without a hidden intercell carry.

There are8t forbidden bits in each Boolean field and2t in the mixed field:

    popcount(M)=18t,
    log2(Lambda)=27t,
    log2(Lambda)+popcount(M)=45t=log2(D0).                    (9)

For arbitrary0<=P,M<Lambda, the proved carry lemma in
[the threshold-mask note](EXPLORATION_LIFE_THRESHOLD_MASKS.md) gives

    popcount((Lambda-P)(Lambda-1)+M)<=45t,
    equality iff P AND M=0.                                 (10)

It includes overflow P+M>=Lambda. Binary factorial valuations identify
popcount(r) with v2(binom(2r,r)). Consequently (7) and (9)--(10) prove
the mask condition; they do not merely assume a successful digit test.

If a surrounding source additionally makes Y the Boolean target word
of these t cells and S the actual inclusive sum of B and its eight
Boolean neighbors, every digit of V is v' from section1. There is no
radix512 carry because every candidate digit lies in[41,429]. The mask
then proves exactly the Life relation at every cell. Conversely, correct
Life data select the unique Boolean helper on each cell.

Neither the interpretation of S nor the typing/periodic repetition of Y
is proved by these twelve equations. In particular this component cannot
replace an actual torus-neighbor construction by an unconstrained S.

## 5. Full positive converse at the new odd index

Take q=512^t and correct finite local data with B>0 and Y>0. Assume S
has the stated inclusive meaning. Choose the unique helper U from the
scalar table. A live output has u=1 and inclusive sum at least3, so
Y>0 implies U>0 and S>0. All seven outer coordinates are positive when
J and r are set by (1)--(2). The raw bounds and exact mask test hold,
so D0 divides the central binomial coefficient.

P is even because its low field is2B and q is even. M is odd because
its low mask digit509 is odd and J is odd. Hence r is odd. This fixes
the negative signs in the retained43-operation auxiliary block.

For clarity, the sixteen fresh positive witnesses can be specified
exactly. Write I=2r+1 and use the standard Pell sequences chi,psi:

    X=2^I, Z=floor((X+1)^(2r)/X^r), w=X/D0, s_p=Z/D0,
    a=Z(X+1), A_p=a+2, Delta=A_p^2-1, P_p=2XZ^2+1,
    c=psi_(A_p)(I), d=chi_(A_p)(I), k=psi_(P_p)(r+1),
    eta=c-Zk, zeta=k-eta,
    tau=(chi_(P_p)(r+1)-1)/2, h=(k-r-1)/(XZ),
    gamma=(d-X-ac)/(4a+3),
    m_aux=2cI, f=chi_(A_p)(m_aux), R_aux=Delta psi_(A_p)(m_aux),
    i=R_aux/c^2, u=chi_(R_aux)(I)/R_aux, y_aux=psi_(R_aux)(I),
    j=(u+I)/c, o=(u+c)/f.                                   (11)

By (5), D0<r^2<X. Since D0 and X are powers of two, w is positive
integral; the binomial congruence gives positive integral s_p. The retained
ratio, Pell and exponential proofs establish positive integral values
of eta,zeta,tau,h,gamma and the remaining main coordinates. The auxiliary
construction makes c^2 divide R_aux. Since r is odd, its normalized-root
congruences are u=-I modulo c and u=-c modulo f. Thus j,o in (11) are
positive integers, and u=jc-I=of-c. These are exactly the fixed-minus
equations from [the odd-index proof](EXPLORATION_ODD_INDEX_PELL_SIGNS.md).

The witnesses are chosen at this new actual index, not reused from the26
packing. They satisfy all ten kernel equations. Their enormous integer
values are specified and proved to exist, rather than materialized by
the finite checker.

The converse intentionally requires nonzero B,Y. All-zero planes cannot
be represented by the strictly positive variables here. A global neighbor
construction may imply B>0 from a nonzero target, but that implication and
any reduction to nonzero targets are not assumed without their own proof.

## 6. Complete arithmetic ledger

The wrapper operations are:

| Part | M | A | Total |
|---|---:|---:|---:|
| q2=q*q, Lambda=q2*q, D0=Lambda*q2 | 3 | 0 | 3 |
| 511J=q-1 | 1 | 1 | 2 |
| V from its five products and four additions | 5 | 4 | 9 |
| P: qU, add the existing2B, q2*V, final addition | 2 | 2 | 4 |
| M:510q,144q2, two additions, multiply by J | 3 | 2 | 5 |
| index right side: two differences, product, addition | 1 | 3 | 4 |
| **Wrapper** | **15** | **12** | **27** |
| Fixed-minus kernel | 25 | 18 | 43 |
| **Combined component** | **40** | **30** | **70** |

The two free outer comparisons are (2). The ten kernel comparisons are
the unchanged first norm, ratio gaps, first-index congruence, a-definition,
exponential congruence, main norm, relaxed auxiliary norm, normalized-root
norm and signed normalized-root congruence. The checker prefixes kernel
names to separate their s,w,U,Y notation from the Life words.

All twelve independently written polynomial residuals are checked. At
zero-based full-source index10, the computed residual differs from the
written normalized-root residual by source9 times (u^2-y_aux^2), the
retained acyclic auxiliary-norm correction. All other residuals agree
literally. The scale used throughout is the computed q^5.

The saving from the proposed28 wrapper is exact sharing: the local
schedule already computes2B, so putting2B in the low field avoids another
doubling. The earlier conditional26 uses a cheaper mask but does not force
its raw field bounds. This27 source pays one more operation and proves
those bounds and radix recovery using positivity and the retained kernel.
Neither70 nor the earlier conditional69 is a complete torus count.

## 7. Finite evidence and remaining scope

The checker verifies the27,43 and70 schedules and all twelve full source
residuals. Its2,500 arbitrary positive-field samples include1,253 positive
indices, of which1,228 have non-power q. These test the pre-kernel bounds
without digit typing. The1,247 nonpositive-index samples are rejected;
they are not kernel solutions. One hundred endpoint checks retain the
important distinction between P<=Lambda and P<Lambda.

There are180 strictly positive packed outer tuples:80 correct and100
with a corrupted output or helper. The checker verifies the exact mask
threshold, odd parity, and nonsquare-scale bounds. It also exhausts all
1,536 one-cell raw field extractions independently of prior Boolean typing.
Correct cases have the fresh positive kernel extension proved in section5;
the finite tests do not materialize those enormous auxiliaries.

The maintained26 source is untouched. Actual spatial neighbors and seams,
target repetition over unbounded witness periods, a uniform raw-input
loader, and any zero-plane accommodation remain outside this component.

Review status: author and two independent complete scoped proof/source
reviews pass. Fresh read-only verification exactly matches the saved JSON.
The independent reviews cover the positivity bootstrap, nonsquare scale,
source ledger, exact mask extraction, and all positive converse formulas.
