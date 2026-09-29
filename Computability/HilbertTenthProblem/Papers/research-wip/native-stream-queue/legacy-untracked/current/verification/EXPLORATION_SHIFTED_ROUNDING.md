# Sharper rounding after the shifted first Pell parameter

This is a supplementary exploration note. It does not change the
112-operation certificate or its already verified proof files.

In the notation of `../1980/PELL_SHIFTED_BASE_PROOF.md`, the shifted
parameter P=1+2UM^2 gives

    0 < xi-C/K < 6/(U+1) < 6/U

before the rounding conclusion. This uses only the exact Pell indices,
the positive interval Y<C/K<Y+1, and xi<3Y. The first exponential
relation bw=2^(2R+1) has already supplied U>4*2^(2R).

Consequently the binomial fractional tail satisfies

    0 < xi-floor(xi) < 1/4,
    xi-floor(xi) >= binom(2R,R-1)/U >= 2R/U > 6/U,

because R>=8. Therefore

    floor(xi) < C/K < xi < floor(xi)+1.

The positive interval itself then forces Y=floor(xi), without invoking
parity. The second exponential relation q=B^L may be established before
or after this rounding argument; its size bound A>R U^R was proved
beforehand in either case.

This observation does **not** allow an odd encoding radix: the separate
binary no-carry argument still needs B to be a power of two after b has
been decoded. It also does not remove either side of the positive
interval. A lower bound alone would permit other integers below the
floor, and an upper bound alone would permit other integers above it.

## Local transformations examined without a saving

The affine chi coordinates d-c(a-2) and d-c(a-1) shorten the base-2
exponent congruence. Reconstructing d for its norm and for the signed
final Pell equation consumes the saved operations. Expanding the norm
directly in the new coordinate is more expensive.

Using the previous Pell denominator a*c-d replaces the affine expression
d-c(a-2) by 2c-(a*c-d), but it also requires reconstructing the required
coordinate c and its first coordinate in other equations. This gives no
net saving, and the unchanged odd-index hypothesis of the signed Pell
block cannot simply be transferred to the preceding, even index.

For the shifted first Pell parameter P=X+1, replacing tau by the
positive quotient t=(tau-1)/X transforms its norm into

    t*(X*t+2)=(X+2)*k^2.

Both the old block and this block require six operations, counting the
Pell coefficient construction. This is an exact tie, even before any
additional use of tau is considered.

None of these observations is a lower bound on the optimal certificate
size. They only account for these particular transformations.
