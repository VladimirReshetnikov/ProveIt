# A congruence class replaces the odd-square radix in the factorial-free source

## Scope, attribution, and concrete endpoints

This is a new composition of two incoming constructions at ProveIt commit
`7a8da414376a80b90ecf799f37ceb26fb9ac674e`. It is not a claim to originate
the negative-radix argument. The **Shared Factorial Error** submission uses
signed binomial digits and the affine odd radix `q=2z+1`; its additional
factorial normalization `Bv=M` rules out both unit radices. The
**Factorial Free Binomial CRT** submission removes factorial authenticity,
but keeps `q=(2z+1)^2`. Here the latter guard is replaced by

    q = 4z+1,       z in Z.                         (AR)

This congruence excludes `q=0,-1,-2` without an extra inequality. It allows
all the canonical completeness witnesses of the factorial-free source.
The new sign proof below transfers negative-radix digit recovery to that
source, which has no `Bv=M` equation.

The literal transformations in `affine_radix.py` give:

| Endpoint | Integer variables | Rows | Degree | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| Factorial-free parent principal | 242 | 178 | 4 | 5018 | 7968 |
| Affine-radix principal | 241 | 177 | 4 | 5067 | 7968 |
| Factorial-free parent dense | 241 | 177 | 4 | 12774 | 7968 |
| Affine-radix dense | 240 | 176 | 4 | 12812 | 7968 |

The arithmetic improvement removes a coordinate and a quadratic row, at
the cost of 49 or 38 collected monomials. The maximum residual coefficient
remains 64. The new principal also has fewer rows, terms, and smaller height
than the Shared Factorial Error balanced 241-variable equation
(178/5351/15107). The dense point trades larger coefficient height for
fewer rows and terms against that submission's 240-variable equation
(177/21482/6144). No global minimum is claimed.

## Inherited source boundary

The factorial-free proof supplies signed Pell certificates for eighteen
power requests. Before any radix or binomial sign recovery, the square
frame and orientation argument establish all relevant Pell coordinates
at their requested signed indices. Its elementary exact-power consequence
is valid for every signed base `n` with `|n|>=2`:

    a certified request (n,k,m) forces k>=0 and m=n^k.

It is important here that the statement allows negative bases. It follows
from the same congruence modulus `T_n=2An-n^2-1`, its unit property modulo
`n`, and its absolute size larger than the possible error. The parent
report explicitly proves that signed-base statement. The unit-base cases
need not be used in the new bootstrap, because (AR) excludes the
degenerate bases before they arise.

The unchanged semantic front is

    t=16+h^2,  d=2(t+1),  F=d^t,
    y=F(2v+1)^2,
    H=2+C+sum(A_j : j=1,...,8),
    B*h_B=C+F^2+1,
    N=B^x,  q=(BH)^x,
    x=F+1+(y+1)u_0,
    x=1+[1+(t+1)y]u_t.

The symbols for powers denote the conclusions of literal polynomial
certificates, not variable-exponent operations in the final equation.
All nine actual CRT representatives are numerator exponents at base `q+1`.
The exact binomial digit uses upper index `F^2+t` at the same base.

The common denominator is `M=q^x`. A normalized remainder `rho_i`
belongs to denominator `D_i` and satisfies a ratio equation
`D_i*v_i=M` and its scaled digit equation. The common norm is

    M^2 = 1+4 sum(rho_i^2)+a^2+b^2+c(c+1).

It gives `M!=0` and `|rho_i|<|M|/2` before signs are known.

## Soundness: signed radix first, positive radix afterward

### 1. Nonnegative representatives and a positive amplifier

The first power request has positive base `d>=34` and index `t>=16`.
Hence `F=[2(t+1)]^t>2^32` and `y>=F>0` independently of every digit.
Equation (AR) says `q` is an integer congruent to one modulo four. Thus
`q+1` is congruent to two modulo four and satisfies `|q+1|>=2`.
Every numerator power request therefore forces its actual upper index
to be nonnegative. In particular `C,A_j>=0` and `H>=2`.

The index equation excludes `B=0`, since `C+F^2+1>0`. Consequently
`|BH|>=2`, and its signed-base power request gives `x>=0` and
`q=(BH)^x`. The last endpoint excludes `x=0`, because
`1+(t+1)y>1` cannot divide `-1`. Thus `x>0`.

If `u_0<=-1`, the first endpoint gives `x<=F-y<=0`, a contradiction.
So `u_0>=0` and `x>=F+1`. The last endpoint now has `u_t>=1` and gives

    x >= (t+1)y+2 >= (t+1)F+2.

Set `Q=|q|`. Then

    Q=|BH|^x >= 2^x >1,      |B| <= |BH| < Q/2.

This also excludes the remaining possible unit `q=1`. All denominator
requests now have genuine signed powers at base `q`, whose magnitude is
at least two. None of these steps assumes the sign of `B` or `q`.

### 2. The first binomial digit works at either sign of q

Put `n=F^2+t` and `C_j=binom(n,j)`. As in the factorial-free parent,

    max(C_j : 0<=j<=t) <= (F^2+t)^t <= 2^(t(F-1)).

Together with `Q>=2^x` and the amplifier lower bound, this gives

    C_max/(Q-1) < 1/32,      C_t < Q/32.

The signed low polynomial

    r* = sum(C_j q^j : 0<=j<t)

is an integer, is congruent to `(q+1)^n` modulo the possibly negative
integer `q^t`, and has

    |r*| <= C_max sum(Q^j : j<t) < Q^t/32.

The ratio and scaled digit equations give an integer remainder `r`.
For completeness, write the scaled row as

    v U = M K + rho,       M=D v.

The right identity shows `v|rho`; `v!=0` because `M!=0`. Thus
`r=rho/v` is an integer and `U=DK+r`. Moreover the common norm gives
`|r|<|D|/2`. Applied to the exact `B` digit with `D=q^t`, this gives
`r congruent to r* modulo D`. Their difference is a multiple of `D`
of absolute value less than `(1/2+1/32)|D|<|D|`. Hence `r=r*`.

Subtracting that low polynomial and dividing by `q^t` proves

    B congruent to C_t modulo q.

Since `|B|<Q/2` and `0<C_t<Q/32`, the difference `B-C_t` has absolute
value less than `Q`; it is therefore zero. Consequently

    B=binom(F^2+t,t)>0,       q=(BH)^x>0.

The negative-radix alternatives have now been excluded by the arithmetic.
They were allowed only during the sign recovery argument.

### 3. Remaining inherited arithmetic and logical decoding

At this point all signs and exact-power meanings required by the
factorial-free parent are available. Its remaining proofs apply verbatim:
recover all other low residues from the `1/32` margin; apply the binomial
prime-power CRT compiler; interpret the bounded local C222 rows; exclude
the boundary `y=F` by propagation of the zero accumulator; recover
label multiplicities by equality of bounded coefficient polynomials;
and apply single-conclusion Horn flow. This yields a finite C222
refutation, and the retained C222/ZF/ZFC calibration yields a finite
syntactic ZFC refutation.

This is an equivalence of existence of witnesses. It is not a pointwise
map to every old square-radix witness: an arbitrary new solution need
not have square `q`. Such a map is unnecessary for the theorem.

## Constructive completeness

Start with a finite C222 refutation and use exactly the canonical witness
construction in the factorial-free report. It chooses `B,H` odd and `x`
even, so `q=(BH)^x` is an odd square. In particular `q=1 mod4`, and

    z=(q-1)/4

is an integer satisfying (AR). All other source witnesses are unchanged.
No new CRT condition, power request, parity restriction, or size
requirement is introduced. The old `z` that parametrized the odd square
is replaced by this new `z`; it occurred nowhere else.

The new graph therefore has an integer zero if and only if a finite
syntactic ZFC refutation exists. ZFC formalizes the elementary algebra,
Pell and binomial arguments and the inherited calibration; negating the
existential statement gives the requested equivalence with Con(ZFC).
No new proof-assistant formalization is supplied by this transformation.

## Exact finite equation transformation

In each supplied final endpoint, the stored coordinate named
`pow2.output` is the semantic `q+1`, due to the parent's translation.
The only row containing the private odd-square parameter is therefore

    q_stored - 4z^2 - 4z - 2 = 0.

The new row is

    q_stored - 4z - 2 = 0.

Its coefficient on `q_stored` is one, so substitute
`q_stored=4z+2` in every other residual and delete the row and coordinate.
This is an integral bijection between the changed graph and the emitted
graph; its inverse restores that coordinate by the displayed affine
polynomial. Every residual remains quadratic. Summing their squares
gives each complete quartic in the accompanying JSON files.

The parent final row operations do not use or change the private radix
row, so the change can be made on the final endpoint without undoing
all preceding transformations. The stored raw-to-final certificates fix
the semantic shift `q_stored=q+1`. The finite checker independently
verifies the changed row, the affine substitution, all coordinate indices,
and every collected coefficient.
