# Reordering the binary pairs and sharing a product: 95 operations

The complete binary tag interface has a **95-operation** schedule:
**51 multiplications and 44 additions/subtractions**, with 28 positive
unknowns and 17 equations. It saves one multiplication from
`EXPLORATION_SHARED_BINARY_TAG_PACKING.md` by changing the pair order so
the product q*M1 serves both packs. The six pair orientations and the
encoded-instance promises remain unchanged.

The packed values and index do change. The proof below establishes the
pre-kernel bounds for the new order and supplies fresh positive Pell
witnesses. It does not claim an identity of the old and new auxiliary
tuples. The result remains four operations above the normalized ternary
91-operation route; no optimality or raw numerical-input construction is
claimed. Both published binary predecessors are unchanged.

## 1. New order and exact schedule

Use all fixed coefficients, positive supplied coordinates, and computed
values of `EXPLORATION_BINARY_TAG_AND_KERNEL.md`, in particular

    R=kD, N=2Tcontent+S1, M1=Q+S1, L=Nsum+H,
    n=q^6, scale=n^2=q^12.

The six paired block coefficients, from lowest to highest, are now

| Pair | S coefficient | W coefficient |
|---|---|---|
| Head partition | S1 | H |
| Prefix partition | E | cH |
| Marker partition | M1 | L |
| Projector guard | Q | Q+AH |
| Projector marker | Q | Q+M1 |
| Content partition | N | Nsum |

Thus

    S=S1+qE+q^2 M1+q^3 Q+q^4 Q+q^5 N,
    W=H+q(cH)+q^2 L+q^3(Q+AH)+q^4(Q+M1)+q^5 Nsum.       (1)

Compute the already-paid q2=q*q and q3=q2*q before packing. Put

    qp1=q+1, Qband=qp1*Q, X=q*M1,
    S_high=Qband+q2*N,
    S=S1+q(E+X)+q3*S_high,
    W_high=Qband+(AH+X)+q2*Nsum,
    W=H+q(cH+q(L+q*W_high)).                       (2)

These are unconditional polynomial identities for (1). The single X
appears in the low marker coefficient of S and the high projector-marker
coefficient of W. Both complete packs cost **9M+11A=20 operations**,
versus the predecessor's 10M+11A. No variable power or multiplication
by a fixed coefficient is free; q2 and q3 each appear exactly once in
the complete DAG.

The complete ledger is

| Portion | Multiplications | Additions | Total |
|---|---:|---:|---:|
| Derived coordinates, transports, cH | 8 | 9 | 17 |
| Shared-product geometry | 3 | 2 | 5 |
| Both reordered packs | 9 | 11 | 20 |
| q^2,q^3,q^6,q^12 | 4 | 0 | 4 |
| Packed complement and index | 2 | 4 | 6 |
| Base-two Pell kernel | 25 | 18 | 43 |
| **Total** | **51** | **44** | **95** |

## 2. Complete source and noncircular bounds

Retain the seven outer equations

    D(Tcontent-E+Ut M1)=N-Ni,
    D(L+(B-1)M1)=L-Li+2q,
    S+Tplus=W+1,
    RH=H+q-1,
    RH=C(AH),
    Rv=q,
    r=(n-1)(n(W+1)+Tplus),                          (3)

with the new definitions (1). Retain the identical ten base-two
43-operation kernel equations at scale q^12. All 28 supplied coordinates
are positive, as before. Only source polynomials 2 and 6, numbered from
zero, change when expanded in the supplied coordinates. Every other
source polynomial is exactly identical to binary97.

The initial geometry argument is unaffected: k is even, so R and q are
even, H is odd, and C(AH)=RH with C a power of two forces C|R before the
kernel. Recover the positive integer A=R/C and AH=A H. The fixed bound
on C and the length equation bound every W coefficient below q. The
reordering does not change that collection of coefficients, so 0<W<n.

Positive S,Tplus and their sum comparison give S<n. Content is still
the highest S coefficient, so q^5 N<=S<n proves N<q. The unchanged
content equation then bounds E<q, using Ni<Li and the same fixed
margin. All S coefficients are nonnegative and below q before invoking
the kernel. No positivity of an omitted complement has been assumed.

Set T=Tplus-1>=0. Then S+T=W<n, and (3) gives

    r=S(n^2-n)+(T+1)(n^2-1),
    n>=64, n<=r<2n^3.

These are the same pre-kernel hypotheses as in the complete binary97
proof. The kernel recovers q as a power of two and the exact central
binomial divisibility. The digit-sum identity forces S&T=0, so S is
a bit-subset of W. Since both have bounded q-coefficients, their six
individual blocks recover, in the order of the table, precisely

    S1&(H-S1)=0, E&(cH-E)=0, M1&(L-M1)=0,
    Q&AH=0, Q&M1=0, N&(Nsum-N)=0.

All four complementary words are nonnegative and bounded. These are
exactly the predecessor's six AND predicates, merely reordered.
The restored true-power row geometry and the unchanged transports
therefore have the same first-short-row halting proof. The initial width
margin and positive-startup promises are unchanged.

## 3. Positive converse and changed index

Given a promised genuine singleton-zero halting run, use the same
ordinary binary row words, fixed C, and sufficiently wide A as in the
predecessor. Form the new S,W by (1), then set

    Tplus=W-S+1,
    r=(n-1)(n(W+1)+Tplus).

The same six ANDs give S<=W<n and positive Tplus. The first pair remains
(S1,H). A true initial zero therefore makes S1's unit bit zero and H's
unit bit one; T=W-S is odd and Tplus is even. Since n is even, r is even.
This works for either parity of beta and introduces no additional
runtime parity operation or post-halt continuation.

The new index has exact valuation 2log2(n), lies in the required range,
and uses the same power-of-two scale n^2. The full positive-converse
construction of the retained base-two43 kernel consequently supplies
sixteen fresh positive auxiliaries. The old auxiliary values are not
asserted to satisfy this changed-index kernel. This proves completeness
with exactly the predecessor's encoded-instance promises, including the
source-supported normalized Neary instances in that scope.

## 4. Exact source and fresh regression

The maintained checker is
`../verification/explore_reordered_binary_tag_packing.py`; its adjacent
JSON serializes the complete 95-operation schedule. It proves (1)-(2)
symbolically, checks all seventeen fresh source comparisons, and checks
that only the two packing-dependent source polynomials change. The
retained triangular norm correction is at comparison 15 and uses the
exact preceding auxiliary-norm source 14 times `(z^2-y^2)`.

The fresh complete regression constructs 88 positive canonical histories
with 382 genuine source rows and 48 odd-beta histories. It verifies the
old and new seven-equation outer schedules separately, all six new ANDs,
all pre-kernel bounds, and both exact index valuations. All 88 new
indices change and remain even. The numerical tests do not materialize
the enormous new Pell auxiliaries; their full positive existence follows
from the general converse in Section3. There is no same-index or
same-auxiliary-witness shortcut.

Review status: author and two independent complete proof/source/dependency
reviews and fresh verification PASS, with no findings. The two predecessor
sources remain unchanged.
