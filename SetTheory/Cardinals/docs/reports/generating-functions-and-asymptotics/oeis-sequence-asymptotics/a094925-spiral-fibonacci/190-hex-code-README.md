# Mathematical code

## Independent sequence constructions

spiral.py supplies delay_table(R), values(rows,a0=0,a1=1), and
coordinate_model(R,a0=0,a1=1). R is a nonnegative integer; a0 is a nonnegative
integer and a1 a positive integer. Booleans, floats, and malformed row indices
are rejected explicitly. The table covers recurrence indices 0 through
U_R=3R^2+4R+2 inclusive, with E0=E1=E2 empty.

The coordinate implementation walks the six triangular-lattice directions,
looks up previously occupied neighboring coordinates, and sums their values.
It does not call the delay table or its value recurrence. The verifier compares
both the entire neighbor tables and both resulting sequences at stage 100.
The shorter original 1,162-row replay is separately retained.

## Exact certificate arithmetic

exact_arithmetic.py represents a+b*phi with Fraction coefficients and relation
phi^2=phi+1. Only int/Fraction coefficients and integer exponents are accepted.
The enclosure evaluates the sign of b before choosing rational phi endpoints.
At stage R>=1 the integer sequence terminates at N=U_R. It forms

    c_N = phi^(-N) (a_N phi+a_(N-1))/(2phi-1)
    T_R = phi^(-6(R+1)) [phi^7(R+1)-phi^6+2phi/(1-phi^(-6))]

The proof in Report190 gives c_N <= C <= c_N/(1-T_R) if T_R<1. A dyadic
square-root bracket is computed by isqrt(5*2^(2P)), P=2N+512. If c_N is
in [cl,ch] and T_R in [tl,th], the outward certificate is [cl,ch/(1-th)].
The original-index A094925 amplitude divides the lower bound by phi_upper
and the upper bound by phi_lower. No floating-point computation is involved.

independent_certificate.py imports neither the primary arithmetic nor its
certificate function. It uses Fraction pairs in the basis 1,sqrt(5), the
relation sqrt(5)^2=5, recursive exponentiation, and a separately derived
arithmetic-geometric tail sum. It receives only the coordinate-generated last
two sequence integers and R. Its center, tail, and complete rational bounds
are compared exactly with the primary computation.

## Exact first correction

first_correction(R) computes eta_n, the entire future tail T_n, the stable
filter H_n=rho H_(n-1)+eta_n, and F1(n)=-alpha T_n+beta H_n. R must be a
positive integer. The future tail beyond U_R is summed by the algebraic
full-stage formula, so the result is exact, with no omitted future terms.

The verifier checks the independent explicit side/corner tail formula at
all 1,159 noninitial rows through stage 19, and checks direct operator sums
and stable convolutions at 82 initial/side-start/corner sample indices. These
checks include side 4's extra step and the degenerate first stage. There is
no implemented all-order interval evaluator; the higher-order script below
is a separate noninterval diagnostic.

## Receipt and validation scope

check_exact.py always uses stage 100, N=30402, P=61316. The fixed stage prevents
an unnoticed lower-precision run from replacing the declared certificate.
It validates the fixture schema, exact counts/types/offsets/source URLs and
pinned SHA-256, then checks the 79 integer terms and 183 source amplitude digits.
All three exact intervals certify 120-place truncations by equal integer floors.
Every 110-place printed pair shares only 109 fractional digits. Exact endpoints
are included as numerator_hex/denominator_hex; Python's int(text,16) recovers
them without a decimal conversion limit. The receipt gives the formulas and
outward rules needed to reproduce them.

There are 83 rejection tests covering booleans and floats, negative or zero
parameters, malformed neighbor rows, zero denominators, reversed intervals,
incorrect fixture schemas and source URLs, digit lengths, duplicate JSON keys,
nonfinite JSON values, and well-typed integer/digit corruption. Check failures
raise exceptions; there are no assert statements removed by python -O.

These finite checks do not prove the mapping lemma, asymptotic hierarchy,
uniform remainder, sharp envelopes, or inverse claims. Those are proved in the
manuscript. Certificate validity uses its proved positive-tail bound; digit
checks use the computed rational bounds directly.

## Optional floating diagnostic

    python3 -B code/diagnose_float.py --stage 100 --dps 180 --order 3

This separate script needs mpmath. It computes finitely truncated operator
iterates through any requested fixed nonnegative order and reports errors at
25 side/interior/corner sample points. The amplitude and future tails are cut
off at the requested stage. More precision does not remove cutoff bias.
The output is explicitly DIAGNOSTIC_ONLY and is not an interval certificate,
proof of a remainder, or evidence of convergence with growing order. The
mandatory checker, replay, guard suite, and builder never import mpmath.
