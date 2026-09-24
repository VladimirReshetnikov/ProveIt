# Prefix-first ternary packing: a 90-operation normalized tag certificate

The complete normalized ternary tag certificate now costs **90 operations:
49 multiplications and 41 additions/subtractions**, with 29 positive
unknowns and 18 equations. Fixed numerals and comparisons are free.
The saving from `EXPLORATION_PRODUCT_COORDINATE_TAG.md` is one
multiplication in the packing, with every one of its nine field tests
retained.

Soundness holds on the predecessor's admitted input domain. Completeness
uses its positive-startup and singleton-zero terminal promises and
strengthens the initial prefix from `0` to `00`. Together with a nonzero
initial deleted prefix, this requires beta>=3. Neary's normalized
instances start `001` and have beta=10p, so the entire previously covered
Neary family remains covered. This result does not provide a fixed
universal system accepting an ordinary numerical query without recoding;
the established raw-input universal bound remains 90.

## 1. Full source and the saved multiplication

Retain all constants, positive unknowns and derived coordinates of91:

    K=3^beta, k=K/3, B=3^(a-1), U=value(appendant),
    epsilon=U mod3, Ut=(U-epsilon)/3, cc=(k-1)/2,
    C>max(K^3,3K*3^a,2KU+3), j=(C-C/K)/2,
    M1=2Q+S1,
    N=3T+S1 if epsilon=0, or N=3T-2Q if epsilon=1.

Here C is a fixed power of three, beta>=2 and a>=2. The admitted input
has Li=3^ell, ell>=beta, Boolean ternary Ni with 0<=Ni<Li/2, and
K^2 Li<C. All the supplied unknowns remain strictly positive.

The eight outer equations are unchanged in form:

    kD=R,
    D(T-E+Ut*M1)=N-Ni,
    D[L+(B-1)M1]=L-Li+3q,
    RH=H+q-1, RH=CZ, Rv=q,
    2r+1=q^9+2P, r+betaP=q^9.                    (1)

The sixteen positive auxiliaries and all ten fixed-plus43 Pell
comparisons remain exactly those of91, at scale q^9. The conceptual
fields are the same nine values, placed in this new order:

    Ebar=ccH-E, E, S0=H-S1, S1,
    Q, G=Q+Z, M0=L-M1, M1, GN=N+jZ.             (2)

Thus P is the sum of these fields times q^0 through q^8. Compute it by

    Low=(cc+q^2)H+(q-1)(E+q^2 S1),
    Upper=Q+q(Q+Z)+q^2[L+(q-1)M1+q^2 GN],
    P=Low+q^4 Upper.                            (3)

Expansion of (3) proves (2) even when conceptual fields are signed.
The already-paid q^2 and q^4 are reused. In91 the product ccH was
computed separately; now it is incorporated into (cc+q^2)H.

| Portion | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| New complete nine-field packing | 9 | 10 | 19 |
| Remaining outer arithmetic | 15 | 13 | 28 |
| Unchanged fixed-plus kernel | 25 | 18 | 43 |
| Complete source | 49 | 41 | 90 |

The adjacent checker verifies the full source in both leading branches.
Only zero-based source comparison6 changes as a formal polynomial in
the supplied coordinates. The norm correction at comparison16 is the
same preceding-source multiple used in91. The new index is generally
different, so canonical Pell witnesses are constructed afresh.

## 2. Bounds and kernel soundness before field extraction

The integer-width argument of91 uses only (1): k,R,q are divisible by3,
H=1 modulo3, and CZ=RH forces C|R. Therefore

    A=R/C is a positive integer, Z=AH, D=(C/k)A.  (4)

This precedes all power and digit conclusions. The direct compiled-input
proof applies even when A<=Li. The unchanged length transport and
constants give

    0<L<q/2, 0<M1<q/6, 0<Q<q/12,
    0<S1<q/6, N>-q/6,
    jZ>=(q-1)/3, GN=N+jZ>0.                    (5)

These are precisely the preliminary inequalities of91. In (3), cc>0,
q>1 and all displayed summands are positive by (5). Hence P>0 without
assuming any conceptual field is Boolean or even nonnegative. Positive
betaP and the last two equations of (1) give, with D0=q^9,

    (D0-1)/2<r<D0, r>=27, D0<r^2.               (6)

Invoke the complete fixed-plus43 soundness theorem at these proved
bounds. It does not require an assumed even r. It yields q a power of
three and the central-binomial divisibility. The unit-two mask lemma
then gives

    P Boolean in ternary, P mod3=1, P<D0/2.      (7)

The remainder of (3) after its q^8 GN term is positive. Therefore GN<q/2,
and, by integrality, GN<=(q-1)/2 and N<=(q-1)/2. The unchanged content
transport has the form

    3E=(1-K/R)N-S1+U M1+K Ni/R.

The same length and compiled-input bounds give E<q/2. Consequently every
field in (2) lies in (-q/2,q), with the only potentially negative fields
being Ebar,S0,M0. In particular all these bounds precede field recovery.

## 3. All nine masks and actual halting

Extract q-blocks of Boolean P from low to high. Initially there is no
incoming carry. A negative field w in (-q/2,0) has normalized remainder
q+w>(q-1)/2, which cannot be a Boolean ternary block. Each extracted
field is therefore nonnegative. Its upper bound below q excludes an
outgoing carry. Induction proves all nine individual masks in (2).
The first-unit consequence is now Ebar mod3=1.

The geometry recovers R and A as powers of three and q=R^t. The original
projector argument from91 uses Boolean S0,S1,Q,M1,G, together with
S0+S1=H and M1=2Q+S1. It does not require the initial selector to be zero.
The exclusion of A=1 using positive Q also remains unchanged. It follows
that Gstar=G+S0 is Boolean and below q, restoring the older projector
guard. The length-flow and signed-content induction in
`EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md` now applies to all nine recovered
fields and the unchanged transports. It proves actual eventual halting
of the specified input.

In particular, soundness is obtained from that post-typing semantic
proof. It is not obtained by treating the new tuple as a source solution
of91 with its old packing or by assuming S0 still occupies the unit block.

## 4. Complete positive converse at a fresh index

Take an actual history with the stated positive-startup promises, initial
prefix00 and final word exactly0. The91 construction supplies positive
Q,S1,T,E and, at an arbitrarily wide canonical radix, all other positive
outer coordinates. Its nine fields are Boolean, bounded below q, and
are still the nine fields in (2).

The unit trit of E is the second input bit, hence zero. The unit trits
of cc and H are one. Thus Ebar has unit trit one. In the new order P is
Boolean with P mod3=1, so r=P+(q^9-1)/2 has exactly the required
central-binomial valuation, and betaP=q^9-r is strictly positive.

It remains to choose even r for the fixed-plus converse. Since q is odd,
the parity of a packing is the parity of the sum of its fields and is
independent of their permutation. Thus for each canonical or padded
outer tuple, the new P and91's P have the same parity; their indices
have the same parity as well. The existing wrapped-zero construction
therefore still flips index parity and selects an even index. More
explicitly, with R=3^m, odd m>2(beta-1), h=beta-1 and d=m-h, its added
zero cycle changes the parity by m+(m+1)d, which is odd.

Padding changes neither the initial prefix nor the positive startup
coordinates. At the chosen new even index the established full
fixed-plus43 converse supplies all sixteen positive Pell auxiliaries.
They are not reused from the old index. Every outer comparison and every
kernel comparison is therefore satisfied with strictly positive supplied
unknowns. The arithmetic theorem covers both appendant-leading branches.
Neary's normalized zero-leading instances have initial001, beta=10p and
a singleton-b halt, and satisfy all the stated conditions.

## 5. Verification boundary

`../verification/explore_prefix_first_ternary_tag.py` checks every source
comparison and the complete90 operation ledger, with symbolic fixed
coefficients, in both leading branches. It verifies the new packing
polynomial and that every other formal source residual is unchanged.
The finite histories check all nine masks, all eight new outer equations,
all eight predecessor outer equations at their respective indices,
positivity, scale bounds, exact valuation, parity preservation and parity
flipping by padding. Both leading branches, odd deletion numbers and
appendant lengths2 and3 are included. Simulation cutoffs are explicitly
unclassified. These are ordinary finite tag examples, not materialized
Neary simulators or enormous Pell witnesses.

Author and two independent complete proof/source/dependency reviews pass.
Fresh verification reproduces the saved receipt: 36 source comparisons,
111 histories, 673 genuine rows and 222 canonical/padded outer tuples.
The canonical indices split 50 even and 61 odd before padding; 41
simulation cutoffs remain unclassified. No optimality or new raw-input
universality claim is made.
