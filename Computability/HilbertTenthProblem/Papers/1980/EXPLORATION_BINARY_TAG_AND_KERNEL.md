# Six binary disjointness tests in one positive 97-operation system

This is a complete positive arithmetic interface for a promised family of
encoded binary tag instances. Its exact schedule has **97 operations:
52 multiplications and 45 additions or subtractions**, 28 positive unknowns,
and 17 equations. Six bit-disjointness predicates are implemented by one
retained base-two Pell/binomial kernel. No external AND predicate, word
bound, or nonnegative-coordinate adapter remains unpaid.

The comparison is useful but is not a new best count: this explicit binary
route remains six operations above the normalized ternary 91-operation
route. It is not a lower bound for binary encodings. Neither a fixed
universal appendant nor an ordinary numerical-input loader is claimed.
The fixed coefficients may depend on both the program and its encoded
initial word, just as in the normalized tag-instance scope.

The conditional predecessor is
`EXPLORATION_BINARY_TAG_QUEUE_HISTORY.md`, whose 29-operation component
left six ANDs, geometry, bounds, and positive adapters external. The
present construction keeps all six ANDs. It uses their four known sums
to remove the four complementary supplied words. A final packing
improvement, suggested independently by the affine review lane, supplies
the positive packed complement and places content last; this saves one
addition from the author's initial 99-operation ledger and restores the
content bound before any bit decoding. Sharing the two geometry products
then saves one multiplication. Neither unfinished intermediate ledger is
a dependency of the final source.

## 1. Instance promise and complete source

Use productions `0 -> 0` and `1 -> u`, deletion number beta>=2, and
an appendant of length a>=2 whose first symbol is zero. Ordinary binary
values put the first symbol in the least significant position. Define

    K=2^beta, k=K/2, B=2^(a-1), U=2Ut=value_2(u), c=k-1,
    Ni=value_2(w), Li=2^length(w).

The initial word has length at least beta, begins with zero, and has a one
elsewhere in its first beta symbols. For completeness, require that its
actual halting run reaches the singleton word `0` and executes a one
selection. Soundness only needs the valid encoded initial word and says
that every admitted tuple certifies an actual eventual halt. The
positive-startup and singleton-zero promises restrict completeness, not
the meaning of the decoded transitions.

Choose a fixed power of two

    C > max(16 K^2 Li, 16 K 2^a, 64).

All these numerals are fixed coefficients. Their runtime
multiplications are counted. Supply the twelve positive outer unknowns

    D,AH,H,Q,S1,Tcontent,E,Nsum,q,v,Tplus,r.

Compute

    R=kD,
    N=2Tcontent+S1, M1=Q+S1, L=Nsum+H.

The name AH denotes a supplied positive coordinate. It is not assumed to
be a product until the pre-kernel reconstruction below. The seven outer
equations are

    D(Tcontent-E+Ut M1)=N-Ni,
    D(L+(B-1)M1)=L-Li+2q,
    S+Tplus=W+1,
    RH=H+q-1, RH=C(AH),
    Rv=q,
    r=(n-1)(n(W+1)+Tplus),                         (1)

where n=q^6 and the two six-block words are

    S = S1 + q M1 + q^2 E + q^3 Q + q^4 Q + q^5 N,
    W = H  + q L  + q^2(cH) + q^3(Q+M1)
                                + q^4(Q+AH) + q^5 Nsum.          (2)

There are sixteen additional positive Pell coordinates. With
scale=n^2=q^12, they are exactly the retained base-two 43-operation,
ten-equation kernel from
`../verification/round39_1980_boolean_history_components.py`. Explicitly,
writing its coordinates a0,c0,d0,f,h,i,j,k0,o,s,w0,tau,eta,zeta,gamma,y,

    Up=w0 scale, Yp=s scale, P0=Up Yp^2,
    Delta=a0^2+4a0+3, z=2r+1+j c0,

its equations are

    P0(P0+1)k0^2=tau(tau+1),
    c0=Yp k0+eta, k0=eta+zeta, k0=r+1+h Up Yp,
    a0=Yp(Up+1), d0=Up+a0 c0+gamma(4a0+3),
    d0^2=1+Delta c0^2,
    (i c0^2)^2=Delta(f^2-1),
    Delta(f^2-1)(z^2-y^2)=1-y^2,
    z=c0+o f.                                                   (3)

All supplied coordinates listed for (1) and (3) are strictly positive. Other
expressions, including the recovered four complementary words, are
computed integers; they are not hidden nonnegative supplied variables.

## 2. Pre-kernel bounds, with no complement or power assumptions

Initially R=kD is even because beta>=2, and q=Rv is even. The head
equation makes H=(q-1)/(R-1) odd. Since C is a power of two and
C(AH)=RH, coprimality of H and C proves C divides R, already before
the kernel. Recover the unique positive integer A=R/C. Then
AH=A H and D=(C/k)A exactly. This restores all three old geometry
values without changing the packing or index. It also proves R>=C
and q>=R before the following bounds.

The length equation gives

    (D-1)L+D(B-1)M1=2q-Li<2q.

Consequently

    0<L<2q/(D-1),   0<M1<2q/[D(B-1)],
    0<Q,S1<M1,      0<Nsum<L,
    0<AH<q/(C-1),  0<cH<cq/(R-1).                (4)

The strict AH bound follows from
`A(q-1)/(CA-1)<q/(C-1)`. Our fixed threshold gives D>32KLi,
so L<q/8, M1<q/16, AH<q/16, and cH<q/16, with ample margin.
Thus every coefficient of W in (2) is nonnegative and below q, including
Q+M1 and Q+AH. Therefore 0<W<n, without assuming that q is a power.

The positive packed-complement equation now gives

    1<=S,Tplus<=W<n.

Every term of S is nonnegative. Its highest term is q^5 N, so N<q.
This is the essential order: N is bounded before bounding E or applying
the kernel. The content equation and N=2Tcontent+S1 give exactly

    2E=(1-K/R)N-S1+U M1+K Ni/R.                   (5)

Here R>K, U<2B, hence U M1<8q/D, and
K Ni/R<K Li/C<1/(16K). The input is least-significant-first, so its
initial zero does not imply Ni<Li/2; only Ni<Li is used here.
Since D>32KLi>=512, (5) proves E<q.
Thus all coefficients of S are also in [0,q), before any bit argument.

Put T=Tplus-1>=0. Equation (1) implies S+T=W<n and

    r=S(n^2-n)+(T+1)(n^2-1).                      (6)

Since S,Tplus are positive and below n,

    n>=64,  n^2-1<=r<2n^3,  n<=r.

These are the preliminary hypotheses of the retained base-two kernel;
they use neither an AND test nor decoded row geometry. The first-index,
first-exponent, and rounding portions of `BASE_TWO_PELL_90_PROOF.md`, as
already extracted in the published retained kernel, yield

    Up=2^(2r+1),   n^2 divides binom(2r,r).

Thus q is a power of two. Since R divides q, R is a power of two, and
R=CA with C a power of two makes A one too. Finally
R-1 divides q-1, so q=R^t for a positive integer t, and H is its exact
row-head repunit. No variable exponentiation has been counted as free.

## 3. The single mask recovers all six ANDs

Write n=2^b. Under 0<=S,T and S+T=W<n, (6) has the three n-blocks

    W, n-S-1, n-T-1.

Their binary digit sums give the exact identity

    popcount(r)=2b+popcount(S+T)-popcount(S)-popcount(T)<=2b.

Equality holds exactly when S&T=0. Kummer's elementary central-binomial
identity is v2(binom(2r,r))=popcount(r); the kernel's divisibility therefore
forces equality. Hence S is a bit-subset of W.

Both words have already bounded q-coefficients and q is a power of two.
The subset relation consequently holds separately in their six blocks.
For each block, its S coefficient is at most the W coefficient, and it
is disjoint from their ordinary nonnegative difference. In order, these
are precisely

    S1 & (H-S1)=0,
    M1 & (L-M1)=0,
    E & (cH-E)=0,
    Q & M1=0,
    Q & AH=0,
    N & (Nsum-N)=0.                               (7)

In particular S0=H-S1, M0=L-M1, Ebar=cH-E, and Nbar=Nsum-N are
nonnegative and below q. Their positivity was not assumed to prove the
packing ranges. Their definitions restore all sums and all six ANDs of
the conditional binary29 component. The final target is exactly
Nfinal=0,Lfinal=2, so its terminal slacks are the positive constants
K-2 and 2; they require no supplied adapters or arithmetic comparisons.

## 4. Actual halting, with the stronger fixed input-width margin

The restored binary projector proves every selected marker is a single
power at most A, while every inactive Q,M1 row is zero. The binary29
length-flow proof applies: disjoint M0,M1 and the single initial marker
produce one unbranched increasing path, with a single terminal marker.
No disjointness of shifted successors is assumed in advance.

The old paid Li<A inequality is not used. Instead our fixed C gives
K Li<R and Li<R. Starting from Li, every zero step shrinks the marker;
every one step starts from a projector-bounded marker at most A and
satisfies 2^a A<R. Consequently K times the current marker is below R
until the first marker below K. The path therefore advances exactly one
time row at each genuine source step, as in the binary29 proof.

On those rows the N/Nbar partition and Nsum+H=L give Nrow<current
marker. Reducing the content transport modulo R/K identifies the
initial Ni, since both it and the actual row value are below R/K.
Then reduction modulo K identifies each deleted prefix, and the bounded
nonnegative scalar update identifies the next row up to the first short
marker. The preceding real transition already proves an actual halt;
no assertion about hypothetical later source rows is required.

Thus every positive solution of (1)-(3) certifies actual eventual
halting. This uses the conditional binary theorem's causal argument,
with its initial width premise replaced explicitly by K Li<R, rather
than claiming an unproved positive lift of its old alphaI.

## 5. Positive converse and automatic even index

For a promised genuine run ending in the singleton zero, choose A an
arbitrarily large power of two so every source marker is below A. Set
R=CA, D=R/k, AH=A H, q=R^t, H its repunit, and use the ordinary binary row words from
the conditional predecessor. Set Nsum=N+Nbar and
Tcontent=(N-S1)/2. This is integral row by row. The promised initial
prefix makes Tcontent,E strictly positive; a one selection makes Q,S1
strictly positive. All the remaining supplied outer coordinates are
also positive. Define Tplus=W-S+1. The six genuine ANDs give S&T=0,
T=W-S>=0, so Tplus is positive and every source equation holds.

The first block was intentionally chosen as (S1,H). The initial symbol
is zero, hence S1 has unit zero and H has unit one. Thus T has unit one
and Tplus is even. Since n is even, (6) makes r even. No post-halt
continuation or additional parity computation is required, for either
parity of beta. The six disjointness tests give exact valuation 2log2(n).

The fresh positive-converse construction of the retained 43-operation
base-two kernel now supplies all sixteen Pell auxiliaries: it needs
n a power of two, n>=64, n<=r<2n^3, even r, and n^2 dividing the central
binomial. All have just been checked. This is an existence construction
of new Pell witnesses, not reuse of another packing's auxiliary values.

The source-supported normalized Neary instances, as recorded in
`EXPLORATION_POSITIVE_STARTUP_TAG.md` and
`EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md`, have even beta, initial
`001`, a genuine one selection, a zero-leading appendant, and (after the
specified s congruence) singleton-zero halting. They satisfy these
promises. Here their words are encoded as ordinary binary values. This
compatibility does not supply a fixed universal u or a numerical-input
decoder at zero cost.

## 6. Exact ledger and finite evidence

`../verification/explore_binary_tag_and_kernel.py` serializes the full
97-operation DAG and checks all seventeen fresh polynomial sources.

| Portion | Multiplications | Additions | Total |
|---|---:|---:|---:|
| Derived coordinates, two transports, cH | 8 | 9 | 17 |
| q/head/shared-product geometry | 3 | 2 | 5 |
| Two six-block packs and their two extra sums | 10 | 12 | 22 |
| q^2,q^3,q^6,q^12 | 4 | 0 | 4 |
| Positive packed complement and index | 2 | 4 | 6 |
| Retained base-two kernel | 25 | 18 | 43 |
| **Total** | **52** | **45** | **97** |

The full source check treats the instance coefficients as symbolic fixed
numerals. The only triangular source adjustment is at zero-based
comparison 15: it adds comparison 14 times `(z^2-y^2)`, exactly as in the
retained norm implementation. Comparison 14 is itself exact. The index
identity (6), if compared away from the packed-complement equation,
has the explicit correction

    r_rhs - [S(n^2-n)+Tplus(n^2-1)]
       = -n(n-1)[S+Tplus-W-1].

No unpublished 99- or 98-operation dependency is needed.

Fresh verification runs check 1,446 exact preliminary geometries, with
208 positive coordinate inverses including 151 nonpower radices; 174,251
complete two-word popcount cases, including 28,501 disjoint accepts;
729 complete three-block complement extractions; and 88 complete
positive canonical histories containing 382 source rows, including 48
odd-beta histories. Every canonical tuple passes all seven outer equations,
all six recovered ANDs, every word range, even index, and exact valuation.
The sixteen enormous Pell auxiliary integers are not materialized; their
positive existence is supplied by the general converse above. These finite
tests supplement the proof rather than establish general soundness.

It is not safe merely to merge the two Q tests into Q&(M1+AH)=0:
an inactive row S1=0,Q=M1=A,AH=A passes that merged test because A&2A=0,
although Q&M1 is nonzero. This is a local obstruction to that syntactic
merge, not a lower bound or a full false-history claim. Both tests remain
implemented in (7).

Review status: author and two independent complete proof/source reviews
and fresh verification runs PASS. Published predecessors are unchanged.
