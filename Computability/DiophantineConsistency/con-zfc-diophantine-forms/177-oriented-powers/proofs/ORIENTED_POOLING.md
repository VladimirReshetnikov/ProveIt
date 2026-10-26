# Independent proof audit: one oriented pool for all five bases

Prepared 25 October 2026 as a separate mathematical audit for the current
ProveIt research iteration. This is an ordinary arithmetic proof, not a
proof-assistant certificate. It verifies the new unbounded argument; the
literal coordinate substitution must additionally be checked against the
emitted finite data.

## 1. The general theorem permits zero bases temporarily

Let W be an integer with W >= 258, put b = floor(sqrt(W-1)), and let A be
an integer with |A| > W^W. Let there be at most five blocks, with integer
bases n_j, and at most seventeen requests in total. Each request in block
j has integers m_i,k_i and a canonical signed Pell pair X_i,Y_i at center
A and signed index k_i. Assume

    n_j^2 < W,  m_i^2 < W,  k_i^2 < W.

Write Z_i=A Y_i, U_i=X_i-Z_i, and define the following finite polynomials:

    T_j = 2 A n_j - n_j^2 - 1,
    H_j = sum_i Y_i (m_i-X_i),
    S_j = sum_i ((m_i-U_i)^2-Y_i^2),
    E_j = S_j-2 n_j H_j,
    Omega = product_j T_j.

The sum over i is confined to block j. Every T_j is nonzero. Define

    R = sum_j n_j E_j product_{ell != j} T_ell - z Omega.       (1)

Then there exists an integer z satisfying R=0 if and only if every request
whose base is nonzero is exact:

    m_i = n_j^{k_i} in Q.

When |n_j| >= 2, such an equality automatically implies k_i >= 0.
For n_j=1 or -1, the usual signed-index unit power is intended. A block
with n_j=0 is deliberately unconstrained by (1). Its contribution is zero,
and T_j=-1. No power at base zero is defined or invoked in the theorem.

### Proof of denominator size and sign

For n_j=0, T_j=-1. Otherwise 1 <= |n_j| <= b, n_j^2+1 <= W, and

    |T_j| >= 2|A||n_j|-(n_j^2+1)
          >= 2|A|-W > W^W.

The inequality 2|A||n_j| > n_j^2+1 also gives

    sign(T_j)=sign(A n_j),
    sign(n_j/T_j)=sign(A).                            (2)

Consequently every nonzero summand n_j d_i^2/T_j has the same sign,
irrespective of the signs of the bases.

### Proof of the exact algebraic identity

Set delta_i=m_i-U_i-n_j Y_i=m_i-X_i+(A-n_j)Y_i. Expanding gives

    sum_i delta_i^2 = E_j-T_j sum_i Y_i^2.             (3)

This uses Z_i=A Y_i and no Pell norm equation. Thus (1), after division by
the nonzero integer Omega, says that sum_j n_j E_j/T_j is an integer.
Equation (3) implies that

    Q=sum_j sum_i n_j delta_i^2/T_j

is an integer as well. Zero-base terms are zero.

### Clearing signed indices without assuming any base nonzero in advance

Let J be the set of blocks whose actual base is nonzero and let s=|J|.
The set J is used only in the proof. Define the nonzero integer

    C=product_{j in J} n_j^b,

using C=1 for J empty. For each request in block j in J, define

    d_i=C m_i-(C/n_j^b)n_j^{b+k_i}.                    (4)

Every quantity in (4) is an integer because |k_i|<=b and C/n_j^b is an
integer. The canonical signed Pell recurrence gives

    X_i+(n_j-A)Y_i = n_j^{k_i} (mod T_j).

Negative powers here mean inverses in Z/T_j Z. They exist because
T_j=-1 (mod n_j), so gcd(n_j,T_j)=1. Multiplying by C gives
C delta_i=d_i (mod T_j). It follows that

    Q'=sum_{j in J} sum_i n_j d_i^2/T_j

differs from C^2 Q by an integer, hence Q' is an integer. This argument
requires no pairwise coprimality among the T_j and permits repeated bases
or repeated moduli.

### The unchanged square frame is more than sufficient

For s>=1, all |n_j|,|m_i|,|k_i| are at most b and b>=16. Consequently

    |C| <= b^(s b),
    |C/n_j^b| <= b^((s-1)b),
    |d_i| <= b^(s b+1)+b^((s+1)b)
          <= 2 b^((s+1)b) <= 2 b^(6b).

With at most r=17 requests,

    sum_{j in J} sum_i |n_j| d_i^2 <= 4r b^(12b+1)
        < W^(6b+2) <= W^W.                            (5)

The strict inequality follows from 4r<=68<W, b^2<W and b<W.
For the last inequality, b>=16 implies 6b+2<=b^2+1<=W.
If J is empty, Q'=0 directly and no estimate is necessary.

Since each active |T_j|>W^W, (5) implies |Q'|<1. Because Q' is an
integer, Q'=0. By the common sign (2), every d_i is zero. Division by
the nonzero C in Q now gives m_i=n_j^{k_i}. If |n_j|>=2 and k_i=-h<0,
this would imply the impossible integer identity m_i n_j^h=1. Thus
such indices are nonnegative. This proves soundness.

### Constructive converse

Assume all nonzero-base powers are exact. Canonical Pell congruences give
T_j | delta_i for each such request. Equation (3) gives T_j | E_j.
Therefore

    z=sum_{j:n_j!=0} n_j E_j/T_j

is an integer and satisfies (1). The omitted zero-base terms vanish.
This proves the stated equivalence including all temporary zero cases.

## 2. Application to the authentic 225-variable parent

The source is package 158-pooled-powers at repository snapshot
0c48d332df6b0e50d4e5b6251c531898f5682c72. Its literal equation is
`equation/equation.json` and its readable copy is `equation/residuals.txt`.
The stronger squared-atom frame is documented in
`proofs/POOLED_POWERS.md` and its membership data. The earlier
`inherited/joint_norm245/proofs/BOOTSTRAP_PROOF.md`, Sections 2--4,
establishes that the Pell frame and orientation are obtained before the
arithmetic powers or any deleted positivity guards are interpreted.

In this parent chart the semantic coordinates relevant to the bootstrap are

    F=x2,  F^2=x3,  t=x0,  V=x5,  B=x4,
    x=x1,  N=x18,  q=x102-1,  M=x128,
    A=x142+1,  W=x141,  BH=x194.

The five bases are

    F^2+1, B, BH, q, q+1.

The request counts are 1,1,1,3,11 respectively. The first power is
V=(F^2+1)^t; the next two are N=B^x and q=(BH)^x; the q block includes
M=q^x. The exact affine offsets in all remaining requests must be read
from the retained parent manifest, not inferred from variable names.

### No circularity: the five bases are all nonzero at every final zero

The new theorem initially applies only to requests at actual nonzero bases.
This is enough. Keep all of the following old rows; no deleted power row is
used in their first consequences:

1. R0 gives x3=F^2. R139 gives t=16+x195^2, hence t>=16.
2. R154 is the common normalized remainder norm. It has the exact form

       M^2=1+4(S^2+sum_i R_i^2)+a^2+b^2+c(c+1).

   Since c(c+1)>=0 for every integer c, M!=0 and |S|<|M|/2.
3. R155 and R156 give B v_B=M and F M=v_B V+S.
   Thus B and v_B are nonzero. For the integer s=FB-V these imply
   S=v_B s and therefore |s|<|B|/2.
4. The first base F^2+1 is positive, so the theorem already gives
   V=(F^2+1)^t>=1. This conclusion does not depend on B,BH,q,q+1.

Put u=|F| and b0=|B|. These facts force b0>=2, u<b0 and V<b0^2:
if b0=1, integrality forces s=0 and then V=FB<=u, whereas
(u^2+1)^t>u. If u>=1 and b0<=u, then

    V=FB-s < (u+1/2)b0 <= u^2+u/2 < (u^2+1)^2 <= V,

a contradiction. For u=0, u<b0 is automatic. Finally
V<(u+1/2)b0 <= (b0-1/2)b0 < b0^2.

R138 gives

    BH=B(2(x9+x10+...+x17)-1),

so the multiplier H is odd and nonzero before any CRT representative is
interpreted. Thus |BH|>=2. The theorem now gives both N=B^x and
q=(BH)^x, and forces x>=0. In particular q cannot be zero or -1:
when x=0, q=1; otherwise |q|>=2. Hence q+1 is also nonzero.
All five blocks are therefore active. The theorem supplies every one of
the parent's seventeen exact powers.

The temporary case x=0 is excluded by M=q^x=1 and B v_B=M with |B|>=2.
The remaining parent bootstrap proceeds unchanged. This application does
not impose a new q congruence, positivity guard, parity requirement, or
cofinal witness restriction.

### Restoring all deleted arithmetic certificates

For each singleton request restore T=2An-n^2-1 and its old quotient
by q_old=-delta/T, with the sign checked against the original row.
The canonical exact-power congruence makes this an integer.
For either old pooled block restore

    L=E/T,  K=2H+(2A-n)L.

All old pool rows then hold exactly. This restoration is integral on the
solution set; it is not a polynomial coordinate inverse on every tuple.
Conversely every old solution supplies the new integer z from the
constructive converse. Hence the new and old systems have exactly the
same projections to their retained semantic coordinates.

In fact the forward map can be written as a polynomial without division.
For each old singleton let its private quotient be v_j, with
delta_j+T_j v_j=0. Identity (3) then gives

    E_j/T_j=T_j v_j^2+Y_j^2

on every old solution. Hence an explicit forward lift for the all-five
variant is

    z=sum_{j=0}^2 n_j(T_j v_j^2+Y_j^2)
        +q L_q+(q+1)L_{q+1}.

For the staged variant, use the first sum as z_first and
L_q+L_{q+1} as z_last. For the paired variant below, the unpooled
singleton retains its old v, the weighted pair uses the corresponding
two terms, and the last pool again uses L_q+L_{q+1}. Thus only the
reverse lift invokes the unbounded exact-power theorem; no theorem
about consistency is required for either direction of the algebraic
certificate transformation itself.

The six private singleton coordinates (three moduli and three quotients)
and the four old pool coordinates can be replaced by one z: a saving of
nine unrestricted integer variables and nine residuals, provided a finite
membership check confirms that they occur only in the rows deleted.

## 3. Degree and scope

In the parent chart all n,A,m,U,Y,Z are affine coordinate expressions.
Each T has degree<=2, H and S have degree<=2, and E has degree<=3.
With five blocks the oriented term n_j E_j product_{ell!=j}T_ell has
degree<=1+3+8=12. The z Omega term has degree<=11. Thus the square
of (1), combined with retained quadratic residual squares, has degree
at most 24. Exact degree 24 and collected coefficients require the
literal polynomial check; they are not inferred solely from a DAG bound.

The contribution extends the two-base reciprocal construction of package
168 by using oriented weights, all five bases, and a zero-base-safe
bootstrap. The general use of oriented weights was already suggested in
package 168's final paragraph. Novelty should be described as the completed
all-base construction and its simultaneous bootstrap, not as invention of
the underlying rational integrality principle or literature-wide priority.

The arithmetic equivalence composes with the parent's C222/ZF/ZFC
refutation calibration. It does not assert consistency, global simplicity
minimality, or a newly compiled end-to-end formal proof.

## 3A. Two smaller-degree grouping variants

The same argument admits separate pools; a single global pool is not
essential. Any subset of the five bases may use its own weighted equation
(1) with its own integer z. The theorem above applies to each subset, with
the same original W and A, because its request and block counts only fall.

### First three weighted, last two unweighted

Make one weighted pool for F^2+1, B, BH, and a second pool for q,q+1:

    R_first = sum_{j=0}^2 n_j E_j product_{0<=ell<=2,ell!=j} T_ell
              - z_first T_0 T_1 T_2,
    R_last = E_3 T_4 + E_4 T_3 - z_last T_3 T_4.

Initially the first pool recovers every nonzero-base request among the
first three. The normalization argument in Section 2 makes B nonzero
independently of powers, the first base is positive, and its recovered
power forces |B|>=2. The odd H then makes |BH|>=2. Thus all three exact
singleton requests are recovered. In particular x>=0 and
q=(BH)^x, so q is neither 0 nor -1.

The two nonzero consecutive integers q,q+1 have the same sign; therefore
T_3,T_4 have the same sign. The unweighted last pool is the previously
proved two-base reciprocal equation. For completeness, its proof is the
same rational-integrality argument with C=[q(q+1)]^b. The cleared errors
obey |d_i|<=2b^(3b), whence

    sum d_i^2 <= 4*14*b^(6b) < W^(3b+1) <= W^W.

The rational sum sum d_i^2/T_j is an integer of absolute value below one;
the common denominator sign prevents cancellation. Thus all fourteen last
requests are exact, including the allowed temporary case q=1. The
unchanged normalization subsequently excludes x=0 as before.

Each weighted three-base residual has degree at most 1+3+4=8; the
unweighted two-base residual has degree at most 3+2=5. Their squared sum,
together with the retained quadratic rows, has degree at most 16. Replacing
ten private old coordinates by two z coordinates saves eight variables
and eight rows. Starting from protected P218 this yields 210 variables.

### A weighted pair, a contracted singleton, and the last unweighted pair

One may instead pool any two of the first three bases with weights n_j.
For the remaining first singleton, substitute its explicit polynomial
T=2An-n^2-1 into its original power row delta+T*v=0 and delete only
the coordinate representing T and its definition row. This is an exact
integral monic elimination with polynomial inverse T=2An-n^2-1; it
preserves the old singleton equation even if the base were zero.

The first base F^2+1 is recovered either by the weighted pair or the
unchanged contracted singleton lemma. The same argument then proves
|B|>=2, |BH|>=2, and q!=(0,-1); the last unweighted pair is valid.
No choice of which two first bases are pooled changes the bootstrap.

The weighted pair residual has degree at most 1+3+2=6, the contracted
singleton row at most 3, and the last pool residual at most 5. Thus the
combined polynomial has degree at most 12. The weighted pair saves three
coordinates, the contracted singleton one, and the last pool three, for
seven total: 211 variables from P218. The actual constructor must identify
the retained singleton and authenticate its exact quotient sign.

The algebraic degree ceilings in this subsection become exact degrees
only after checking a nonzero highest homogeneous part in the emitted
literal residual; the accompanying independent checker does so for the
available completed artifacts.

## 4. Failure modes checked in this audit

- Dropping the weights n_j would allow cancellation between positive and
  negative bases; the proof would be invalid.
- Claiming every base nonzero before interpretation of q would be circular.
  The theorem explicitly omits zero-base blocks first, then the retained
  normalization and the first three recovered powers exclude them.
- Squaring denominators without strengthening the Pell congruence is not
  justified: congruence modulo T gives no congruence of squared errors
  modulo T^2. Formula (1) keeps each denominator unsquared in the energy.
- True-power outputs at unit bases do not force nonnegative indices. That
  conclusion is used only for |B|>=2 and |BH|>=2.
- No pairwise coprimality of the five T_j is needed or assumed.
- The square-frame bounds must cover actual affine bases, outputs and
  indices, including F^2+1 and BH, before any power rows are removed.
- The exact quotient sign and affine offsets must be checked separately
  in the final coordinate chart.
