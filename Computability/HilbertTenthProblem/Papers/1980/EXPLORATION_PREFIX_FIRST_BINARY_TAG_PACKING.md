# Prefix-first binary packing on initial-00 instances: 94 operations

The complete binary tag interface has a **94-operation** schedule on
the normalized Neary input family: **50 multiplications and 44
additions/subtractions**, with 28 positive unknowns and 17 equations.
This saves one multiplication from
`EXPLORATION_REORDERED_BINARY_TAG_PACKING.md` by placing the prefix pair
before the head pair and factoring their two denominator blocks.

The general completeness promise is strengthened to an input beginning
`00`, still with a nonzero symbol in its initial deleted prefix, a genuine
one-reading event, and a singleton-zero terminal word. In particular,
beta must be at least 3 for these startup promises. The normalized Neary
instances begin `001` and have beta=10p, so this change preserves that
entire source-supported family. It does not assert the predecessor's
broader completeness for arbitrary first-zero inputs. The normalized
ternary frontier remains 91; no fixed-appendant/raw numerical-input or
optimality claim is made.

## 1. The changed blocks and paid schedule

Use the positive coordinates, fixed coefficients, and equations of the
complete binary97 construction, with its binary95 packing improvement.
In particular,

    R=kD, N=2Tcontent+S1, M1=Q+S1, L=Nsum+H,
    c=k-1, k=2^(beta-1), n=q^6, scale=n^2=q^12.

The block pairs from lowest to highest are

| Pair | S coefficient | W coefficient |
|---|---|---|
| Prefix partition | E | cH |
| Head partition | S1 | H |
| Marker partition | M1 | L |
| Projector guard | Q | Q+AH |
| Projector marker | Q | Q+M1 |
| Content partition | N | Nsum |

Keep the already-paid q2=q*q and q3=q2*q and define

    Qband=(q+1)Q, X=qM1,
    S_high=Qband+q2*N,
    W_high=Qband+(AH+X)+q2*Nsum.

Then compute the exact packs by

    S=E+q(S1+X)+q3*S_high,
    W=(q+c)H+q2(L+q*W_high).                         (1)

Expanding (1) gives exactly the displayed six pairs. The old cH
multiplication is absent from the schedule. The old low denominator
segment H+q(cH+q(L+q*W_high)) costs 3M+3A in addition to cH's 1M.
The new expression for W costs 3M+3A after W_high: q+c, its product with
H, q*W_high, addition of L, multiplication by q2, and the final sum.
The swapped low S segment has the same cost. Thus the complete saving
is exactly one multiplication; it does not treat a coefficient product
or a variable power as free.

| Portion | Multiplications | Additions | Total |
|---|---:|---:|---:|
| Derived coordinates and transports | 7 | 9 | 16 |
| Shared-product geometry | 3 | 2 | 5 |
| Both prefix-first packs | 9 | 11 | 20 |
| q^2,q^3,q^6,q^12 | 4 | 0 | 4 |
| Packed complement and index | 2 | 4 | 6 |
| Base-two Pell kernel | 25 | 18 | 43 |
| **Total** | **50** | **44** | **94** |

## 2. Soundness and pre-kernel bounds

The seven outer comparisons remain

    D(Tcontent-E+Ut M1)=N-Ni,
    D(L+(B-1)M1)=L-Li+2q,
    S+Tplus=W+1,
    RH=H+q-1,
    RH=C(AH),
    Rv=q,
    r=(n-1)(n(W+1)+Tplus).                           (2)

All 28 supplied unknowns are positive, and the same ten base-two
43-operation Pell comparisons are retained at scale q^12. Only the
expanded source polynomials for comparisons 2 and 6, numbered from
zero, change from binary95. The factorization in (1) introduces no new
unknown, comparison, divisibility assumption, or sign condition.

The binary97 pre-kernel argument applies to the permuted coefficient
lists without change. Before invoking the kernel, even k gives even
R and q; the head equation gives odd H, and RH=C(AH) implies C|R.
Thus A=R/C is a positive integer with AH=A H. The unchanged fixed
margin on C and the length equation bound each W coefficient below q.
Consequently 0<W<n, and positive S,Tplus with S+Tplus=W+1 give S<n.
Content is still the highest S coefficient, so q^5 N<=S<n gives N<q.
The unchanged content transport bounds E<q. Hence every S coefficient
is also nonnegative and below q before any power or AND typing.

Putting T=Tplus-1>=0 yields S+T=W<n and

    r=S(n^2-n)+(T+1)(n^2-1),  n>=64,  n<=r<2n^3.

The retained kernel therefore recovers q as a power of two and the
central-binomial valuation which forces S&T=0. Bounded blocks extract
exactly

    E&(cH-E)=0, S1&(H-S1)=0, M1&(L-M1)=0,
    Q&AH=0, Q&M1=0, N&(Nsum-N)=0.

These are the same six predicates as before. The four complements
are nonnegative and bounded, and the unchanged row transports have
the same first-short-row halting soundness proof. None of this
soundness reasoning uses the extra initial-second-zero promise.

## 3. Completeness and the new even index

Take a genuine singleton-zero halting run with the stated startup
promises. The unchanged binary row construction, fixed C, and
sufficiently wide A give all positive outer coordinates and six AND
predicates. Compute the new S,W from (1) and set

    Tplus=W-S+1,
    r=(n-1)(n(W+1)+Tplus).

The six predicates give S<=W<n. To check the sign choice for the Pell
converse, k is even and c=k-1 is odd, while H is odd. The unit bit of
the prefix word E is exactly the initial word's second bit, which is
zero. (Every later row is multiplied by even R.) Thus E is even,
S is even, and W is odd because its lowest block is cH. It follows
that T=W-S is odd, Tplus is positive and even, and r is even.
This works for both parities of beta; there is no parity-padding step.

The exact valuation remains 2log2(n), with the same index range and
power-of-two scale n^2. The retained base-two43 positive-converse
theorem supplies sixteen fresh positive Pell auxiliaries. The block
permutation generally changes S,W,r and those auxiliaries; no old
auxiliary tuple is reused or presumed valid.

The already-established Neary startup is `001`, beta=10p>=10. It
satisfies both the new initial-00 condition and the existing positive
initial-prefix condition. Its guaranteed one-reading event and
normalized singleton-zero halting convention are unchanged. The
complete encoded-instance universality scope is therefore preserved.

## 4. Exact source and fresh verification

The maintained checker is
`../verification/explore_prefix_first_binary_tag_packing.py`; its JSON
records the complete 94-operation schedule. It checks the two pack
identities, all seventeen source comparisons, and the unchanged
triangular norm correction at comparison 15 from preceding source
14 times `(z^2-y^2)`. It also verifies that only the two
packing-dependent source polynomials differ from binary95.

The fresh canonical regression has 144 histories and 464 source rows:
48 odd-beta histories at beta=3 and 96 even-beta histories at beta=4.
It checks both seven-comparison outer sources, all six new ANDs,
positive supplied coordinates, bounded coefficients, both exact
index valuations, and the initial-00 parity argument. All 144 new
indices differ from their binary95 predecessors and are even.
The enormous new Pell auxiliaries are not materialized; their positive
existence follows from the unchanged general converse after every
required new index hypothesis is proved and checked.

Review status: author and two independent complete proof/source/dependency
reviews and fresh verification PASS, with no findings. Published predecessors
are unchanged.
