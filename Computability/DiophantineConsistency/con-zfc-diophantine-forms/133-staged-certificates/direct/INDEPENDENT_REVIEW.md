# Independent mathematical review of the staged common-cap construction

Reviewed files: the staged construction, portable `build.py`, `PROOF.md`,
the staged raw JSON graphs,
the inherited shared-binomial `direct/PROOF.md`, the shared-cap
`portable/CAP_THEOREM.md`, and the inherited simultaneous-power proof.
The literal coefficient checks are performed independently by
`review_staged_independent.py`, which imports no builder or inherited
checking module. The receipt identifies every equation actually checked.
The final review also covers the dominant-modulus change, with its
inherited attribution in `upstream/DOMINANT_MODULUS_PROOF.md`.

## Verdict and scope

The two-stage common-cap argument is sound under the explicitly retained
indexed-Pell lemma and direct-C222 arithmetic/source calibration. I found
no circular inference in the new interpretation order and no obstruction
to simultaneously choosing the cap, all principal Pell pairs, the free
common base, and all natural quotient witnesses.

This is an ordinary mathematical review, supported by exact finite
transcription and polynomial checks. It does not assert an independently
reproved C222-to-ZFC calibration, an end-to-end Lean/Rocq certificate, or a
global simplicity optimum. In particular, re-expanding the final quartic
checks its literal coefficients but cannot establish its unbounded
consistency equivalence by itself.

## 1. What is known before either pooled congruence is decoded

The raw coordinate shifts give `t>=16`, `B>=2`, and the four exact-power
exponents `t,K,y+1,x+1` are positive. The frame is literally two plus the
sum of the twelve distinct base, exponent and output atoms of six exact
power requests. All coordinates are natural. Thus every one of those
atoms is strictly below `W`. This conclusion does not assume the outputs
are already the intended powers.

The first binomial numerator index `F^2+t` is not itself a frame atom.
Nevertheless the **distinct** atoms `F^2+1` and `t` occur, and so

    W >= 2 + (F^2+1) + t = F^2+t+3.

This is the important raw bound for the fifth first-stage seed. The
literal audit checks the defining gates of both expressions. Its
propagation of trivial nonnegative lower bounds also obtains `W>=59`
for the checked chart; the proof uses the weaker sufficient `W>=38`.

The lower-frame norm is at base `W+1`. Since its ordinate is the positive
multiple `WZ` with `Z>=1`, reduction modulo `W` forces its Pell index to
be a positive multiple of `W`. Consequently

    L >= X_W(W+1) >= (W+1)^W,
    A=L+sigma >= L,
    A-1 > W^3.

The inherited complete indexed-Pell certificate at the requested index
`W` is still present. Its required `Ycap>=W` follows from the aggregate
row. It therefore fixes the cap as `Y_W(A)`. Each principal norm then
gives an actual index `j>=0`; the aggregate forces `j<W` by strict
monotonicity of Pell ordinates. No intended second-stage index has been
identified at this point.

## 2. Why the two error rows work

For either group, once the **requested** indices `k` have been shown to
lie in `[0,W-1]`, the row

    sum (Y_k-k)^2 = (A-1)Q

and the recurrence congruence `Y_j(A)=j mod(A-1)` imply

    A-1 divides E=sum(j-k)^2.

There are at most fifteen terms, so

    0 <= E <= 15(W-1)^2 < W^3 < A-1.

Therefore `E=0`, identifying each index individually. The proof does not
need the actual ordinates `Y_j(A)` to be small, and it does not need the
intended indices to be strictly positive. Nonnegative indices work.

The first group has exactly the four power indices and `F^2+t`, all
bounded directly from syntax as above. Decoding it recovers all six
powers. The standard power modulus is positive, excludes base zero,
and exceeds both the proposed output and the actual power because the
frame is exponentially large. The one-sided quotient exists because
the Pell expression is positive and congruent to the least nonnegative
power residue.

At this point the exact power `V=(F^2+1)^t` is positive. The two raw
ceiling rows, before B is interpreted as a binomial, combine to give
`V+slack=BF`, so `F>=1`. The raw endpoint rows give

    y=F+1+r0>=2,
    x=F+1+(y+1)u0>=2,
    x=1+(1+(t+1)y)ut.

The last row forces `ut>=1`; hence

    x>=2+(t+1)y>max(t+1,y+1).

Consequently `q^(t+1)` divides `Dx=q^(x+1)`, and every range
modulus `Nq^k`, for `k=t,t+1,y+1,x+1`, divides the **literal**
common-root modulus `M=N Dx`. This establishes all necessary modular
reductions before decoding the first binomial. The argument uses neither
`F=t!` nor the binomial meaning of B. The independent checker verifies
the actual product gate defining M, both ceiling rows, their combined
identity, all three endpoint rows, all six exact-power identifications,
and every requested denominator and modulus binding.

The exact powers also give `N=B^(2R)` and `q=N^(2R)` with `B>=2`.
Hence `q>=2^(4R^2)`. This bounds the lower coefficients of the first
binomial without knowing the factorial. Its exact digit yields
`B=binom(F^2+t,t)`, and the inherited squared-radius fixed-point lemma
gives `F=t!`.

For the second group, the raw aggregate representative bound gives the
nine independent representatives at most `9N^2`. The positive-DAG
majorant gives

    J <= (9N^2+1)^ell <= N^(3ell).

Neither statement uses any of their range-divisibility conditions.
Only the now-established factorial is needed to obtain
`3ell(t+1)<=2F<K`. Thus every second-stage index is below `q`, and `q<W`
because `q` is a frame atom. The second error row can now be decoded.
This completes the noncircular order.

## 3. Why pooling the unbounded second group prematurely would fail

The explicit toy counterexample `A=100, W=3`, actual index `j=1`,
requested index `k=100`, demonstrates the need for the requested-index
bound. Here `A-1=99>W^3`, `Y_1(100)=1`, and `Y_3(100)=39999`. The cap
aggregate is satisfiable and

    (Y_1-k)^2 = (1-100)^2 = 99*99,

so the pooled divisibility row holds although the index is wrong. This
does not refute either complete construction. It shows why the small
error argument must wait until the second-stage bounds have been proved.
The independent checker records this counterexample as a negative control.

## 4. Simultaneous completeness and the common root

In completeness, all semantic source data, CRT representatives, powers,
and digit denominators are chosen before the common Pell base. They
determine `W` and the modulus `M=N Dx`, which is a power of N because
`q=N^K` and `Dx=q^(x+1)`. Then choose the lower-frame pair at index `W`
to obtain `L,Z`. Since N divides q, `gcd(q+1,M)=1`.

The required common-root congruence is

    2A(q+1) = (q+1)^2+1 mod M.

Since `gcd(q+1,M)=1`, the gcd of its linear coefficient and modulus is
one or two. In the second case `q` is even, so `(q+1)^2+1` is even.
Thus the congruence is soluble, and its solution class contains
arbitrarily large positive values. Choose `A>=L` in that class, also
large enough to make the displayed quotient nonnegative. The slack
`sigma=A-L` is natural. Crucially, the construction does **not** require
this freely chosen `A` itself to be the lower-frame Pell abscissa.

The inherited indexed-cap completeness theorem works for every fixed
`A>=2` and positive `W`. Its auxiliary base can be raised within the
CRT congruence classes to make the oriented quotients natural. Supply
the principal pairs canonically at their true requested indices.
All those indices are below `W`, so with `m=15<=W-2`,

    Y_W(A)-sum Y_k(A)
      > (2A-1-m)Y_(W-1)(A) > W.

Consequently the aggregate slack exists. Each individual difference
`Y_k(A)-k` is divisible by `A-1`; each group sum of its squares has a
nonnegative integer quotient. This constructs both pooled quotients
simultaneously, without bounding them or putting them into the frame.

Every modular numerator `X_n(A)+(q+1-A)Y_n(A)` is positive: it equals
one when `n=0`, and exceeds `qY_n(A)` when `n>0`. Its congruence to
`(q+1)^n` supplies the required low digit or zero-divisibility residue.
The nonnegative quotient then follows from positivity and Euclidean
remainder bounds. No negative quotient is silently represented by a
natural coordinate.

## 5. Allowing zero CRT representatives

This is an optional further simplification discussed during review, not a
change used by any of the four final equation files. No new measured
endpoint is claimed for it here.

Deleting the nine `+1` shifts from the independent CRT representatives
is also valid for this cap architecture. The old strict positivity was
needed by the former indexed-Pell API. Here a requested numerator index
zero is represented by the genuine principal pair `(1,0)`, and the
modular numerator is one. The binomial range lemma already covers
`n<k`, including `n=0`. Exact power exponents remain positive, the
first-stage decoding is unchanged, and the second-stage small-error
proof allows zero requested indices.

The index congruence `B | C+F^2+1` and local polynomial evaluation do not
require `C>0`. Completeness may use the old positive CRT representatives,
which are still allowed. This is existence equivalence through the
decoded proof source, rather than a coordinatewise inverse obtained by
subtracting one from every new representative.

## 6. Exact finite checking

The independent script reconstructs the frame row; lower-frame norm;
free-base and positive-ordinate definitions; all cap norms, divisibility
and oriented congruence rows; all fifteen principal norms; the global
aggregate; both five/ten-member squared-error rows; the raw bound
identities; and the common-root row. The dominant-modulus extension
checks `M=N Dx` in the actual gates, the raw ceiling and endpoint
identities needed before binomial decoding, and every exact-power,
digit-denominator and range-modulus identification. There are 55
individual row/gate checks, plus the stated structural checks.
It independently collects the
sum of squares of the final residuals, checks every coefficient against
the supplied expansion, and recomputes variable liveness, degree, term
count and coefficient height.

It uses explicit exceptions, so `python -O` preserves all checks.
Its finite Pell fixtures verify the cap's constructive slack and pooled
quotient on small examples, and include the missing-range counterexample.
The exact algebra and ordinary arguments above establish the general
claims; the fixtures serve only as regression checks.

The final ordinary and `-O` receipts are
`INDEPENDENT_DOMINANT_RECEIPT.json` and
`INDEPENDENT_DOMINANT_RECEIPT_OPTIMIZED.json`. All four literal expansions
pass, with these independently recomputed metrics:

| Profile | Natural variables | Quadratic residuals | Quartic monomials | Coefficient height |
|---|---:|---:|---:|---:|
| principal239 | 239 | 187 | 20,015 | 84,062,635 |
| sparse240 | 240 | 188 | 12,836 | 84,062,620 |
| minimum237 | 237 | 185 | 69,710 | 133,499,131 |
| small_support255 | 255 | 203 | 5,743 | 64,214,623 |

All four have exact total degree four. The receipts pin their complete
equation JSON bytes. This final modulus reduction preserves the
acyclic staged proof and cofinal common-base completeness.
