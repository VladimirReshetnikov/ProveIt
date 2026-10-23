# Independent arithmetic audit of the round-eight nine-variable construction

## Scope and status

The new quotient-corrected majorant, its margin-first norm finalizer, and the
selective-source/exact-mask interface pass the independent checks below.
`verify_majorant_independently.py` imports no construction program. It reads
the source and certificate JSON as mathematical data, reconstructs their
identities, and emits `INDEPENDENT_ARITHMETIC_VERIFICATION.json`.

This is an ordinary mathematical proof audit with executable finite checks,
not an end-to-end proof-assistant certificate. The native compiler,
calibration and Jones numerical ratio theorem are inherited dependencies.
No assumption of consistency is used in the arithmetic arguments.

## 1. The majorant is unconditional, not only valid on prospective zeros

The mixed-domain source must establish `R,N>=8`, `b,g>=1`, and `b<=R,N`
before the norm equation is considered. With `s,w>=1` this gives

    A=R N^2 s (N^2 w+1)>=8*64*65=33280.

Consequently the majorant proof's weaker hypotheses `A>=729,C>=1,i>=1`
hold at every mixed-domain assignment. In particular it is legitimate to
use the majorant to recover the sign of the margin, rather than using a
margin-dependent bound circularly.

The independent checker reconstructs the four-quotient definition of `T6`
and proves its equality to the operation-saving collected expression in
`ratio_tail.py`. It verifies, after multiplying by the positive denominator
`2D^5`, the complete displayed seventh-order remainder identity. It also
checks the exact square identity for `t7`; that square remainder has seven
strictly positive coefficients. Since the negative coefficients in `t7`
sum to 1719, less than 2048, `t7>0` for `D>=1`. Squaring therefore preserves
the required upper-bound orientation.

For the quotient estimates the checker substitutes `A=729+a` and records
strictly positive coefficient lists for the following numerator differences:

- `A+1-729`;
- `(A^2-1)-(364A-365)`;
- `(A+1)(A^2-1)-A^3`;
- `(A^2-1)^2-64A^3`;
- `4(A^2-1)-(4A-5)A`.

These are certificates on the entire half-line `a>=0`, not numerical
samples. Together with `D=(A^2-1)C^2+1`, they justify every denominator
comparison in the proof. The discarded cubic terms cost at most
`929i^3+14i^3 C+9i^3 C^2`. The discarded linear terms cost less than
`277i`, using

    64+40/9+28/81+21/729<69, 66/9^4<1.

The stated correction supplies the corresponding `14C` and `9C^2` terms
plus `1024i^3+288i+2048`. Thus the bounds leave a strictly positive surplus.

For clarity, the radical comparison uses `X=k^2 D^3(D-1)>0` and
`DF=X+D`. Strict concavity gives

    sqrt(X+D)<sqrt(X)+D/(2sqrt(X)).

Multiplication by positive `2048G`, and the identity
`G=(X/D)L+CD+1`, give the claimed expression with residual
`v=(CD+1)/(2k sqrt(D(D-1)))`. Because `k>=7C,D>=9`, the comparison
`sqrt(D(D-1))>D-1` proves `v<1`. Therefore

    T>2048 sqrt(DF)G>0,
    TH>2048 sqrt(DFI),

where the second strict inequality uses `I=G^2H^2-H^2+1<G^2H^2`.

## 2. Denominator clearing and sign recovery have the correct orientation

Write `q=2048^2`, `Omega=Jm`, `E0=Jn+Q`,
`Theta=E0-Omega(V0+V1)`. The polynomial is exactly

    [Theta^2-Omega^2(a0+q a1)]^2-4q Omega^4 a0a1.

Its four-real-factor identity is verified independently. If `m=0`, its
value is `E0^4>0`. Otherwise a zero gives a signed-root identity

    n+Q/J=m(V0+V1+r0+r1),
    r0^2=a0, r1^2=q a1.

Both strict majorants hold before imposing `m>0`, so the bracket on the
right is positive for every choice of root signs. The left side is
positive because `J,Q>0,n>=0`. Hence `m>0` follows before any integrality
argument. This is the necessary orientation; mere squaring would not
recover it.

The positive margin gives `C>K(Y-1/2)>K`. The elementary ratio inequalities
then give `a1>a0`, so no signed sum `r0+r1` can vanish. Its rationality
forces each root rational, and a rational square root of an integer is an
integer. Dividing `r1` by 2048 gives an integer square root of `a1`.
Consequently the bracket is integral and `J|Q`.

Conversely take positive integer roots. The bound `V1>Q` follows from
`F=1+k^2D^2(D-1)>=D`, `D>C^2`, `G,H>1`, and `Q<3C^2`.
Thus `n=m(V0+V1+r0+r1)-Q/J` is a positive integer whenever the four ratio
conditions hold. No quotient-denominator sign or zero case is omitted.

## 3. Exact degree with independently varying source degrees

Put `r=deg R`, `n=deg N`, `c=deg Gcap`, with positive diagonal leading
coefficients `rho,nu,kappa`. In the intended source families `r>2` and `C`
is led by `2R`. The independent 703-term expansion of
`T^2-2048^2 DFG^2` matches the supplied JSON term for term.

For each monomial `A^a C^d i^j` of that expansion,

    a+d<=33, a<=15, 2a+j<=36.

The simultaneous equalities occur uniquely at `(a,d,j)=(15,18,6)` with
coefficient `9*2^18`. Since its source degree is
`(a+d)r+4an+2a+j`, this proves the exact defect degree
`33r+60n+36` for all positive `r,n`, not merely for the old relation `r=3n`.

The leading registers are therefore

    deg H=17r+32n+19,
    deg Delta1=67r+124n+74,
    deg Omega=5r+20n+c+12.

In the cancellation-resolved inner expression, `Omega^2 Delta1` uniquely
dominates. Its degree exceeds the `Omega^2 V0 V1` term by
`15r+20n+15`, and exceeds the `E0 Omega V1` term by
`23r+48n+c+31`. Squaring the leading inner term exceeds the norm's final
subtracted term by `30r+40n+30`. These differences are strictly positive
for every supplied source. Thus

    deg F9=154r+328n+4c+196,
    leader(F9)=81*2^148*kappa^4*rho^154*nu^328.

For the width-174 unshifted packed source, `r=18386,n=4778,c=349`, giving
the exact degree `4,400,220`.

## 4. Selective source, sparse borrows, and calibrated square threshold

The independent checker reconstructs all 60 original source gates as
symbolic polynomials and substitutes precisely the twelve declared
coordinate shifts. All 22 residuals and all 109 factorial-weighted records
agree literally with the selective source. The accompanying positivity
recovery covers the other nineteen coordinates; in particular `beta,K0>0`
are available from the coherent fixed tuple. The all-zero natural tuple
fails the second source row, whose value is `-1`.

For all nine supplied target schedules, the checker enumerates all 528
padded quadratic monomials and performs 57,552 active-support comparisons.
It checks row signs, target distinctness, every nonnegative encoding
exponent, the actual positive integer leading coefficient of `Dcode`, and
`K>=max H+2`. Full Sidon isolation is not assumed.

The target digit test remains valid across a signed incoming borrow:
`2h+1+epsilon`, with `epsilon` either `-1` or `0`, normalizes to a digit
disjoint from `B-2` if and only if `h=0`. Independent exhaustive checks
include both incoming borrows and zero/nonzero coefficients. The positive
leading coefficient and coefficient bound must be used to establish
`Jcode>0` before identifying the normalized sequence with ordinary digits.

For the nine-variable source, the binary block is specifically
`L=2b B^E`, not the ten-integer branch's `L=B^E`. For `0<=S,T` with
`S+T<L`, set

    R=L^2+(S+T)L+L-1-S.

Writing `L=2^ell`, the exact popcount identity is

    popcount(R)=1+ell+popcount(S+T)-popcount(S).

Its value reaches `1+ell+popcount(T)` precisely when `S&T=0`. This includes
`S=0`, `T=0`, `S+T=L-1`, and the possible power-of-two input `b=1`.
The independent checker exhausts 11,049 such small-block cases.

For 31 coordinates, 22 target cells, `B=2^kappa b^2`, `b=2^k`, the required
threshold exponent is

    kappa(E+W+23)+(2(E+W+23)-30)k-20.

It is even when `kappa` is even. Put `n=E+W+8`, `tau=floor(n/2)`,
`epsilon=n mod 2`. The general literal square-root polynomial is

    N=2^((15+epsilon)kappa/2-10) B^tau b^epsilon.

This parity case is necessary for some supplied target schedules; the
width-174 packed source has `epsilon=0`. It follows that

    deg R=4E+2, deg N=E+W+8, deg Gcap=2W+1.

The source coefficient bounds and arbitrary-input positivity are separate
from the bounded decoding branch. On the latter, the ratio theorem supplies
`g<4bB^W`; on completeness, an encoded source zero satisfies the stronger
`g<bB^W`, yielding `32g<Gcap` for `Gcap=32bB^W`. These two directions must
not be interchanged.

## Reproduction

Run `python audit/verify_majorant_independently.py` from the package root.
Run `python audit/verify_nine_circuits_independently.py` for the composed
literal-circuit check. The latter imports no construction program and
reconstructs the source, ratio registers, uncollected majorant and norm
directly from their displayed definitions.

## 5. Frozen literal composition and fixed-coefficient checks

`INDEPENDENT_NINE_CIRCUIT_VERIFICATION.json` records a passing replay of all
twenty-eight delivered DAGs: twenty primary positive/natural forms and eight
positive cancellation-resolved degree-certificate forms. Each receives 180
direct-formula comparisons, using six moduli (including 2, 3 and 5), the
actual native tuple and an alternate tuple, and zero/one/two/random inputs.
The test compares every available named register as well as the output.
It additionally proves 1,298 exact symbolic register identities at verified
polynomial cut points, including the source block, threshold monomial,
factored majorant and final norm. These checks do not rely on modular
sampling. The source polynomial Dcode itself is independently checked by
the exact coefficient/extraction verifiers.
It verifies the exact domain translations, topological ordering, absence
of dead gates, nine-variable set, binary-operation counts, and target hashes.

All four native coefficient payloads match their pinned raw hashes. Direct
integer evaluation of every weighted coefficient proves the maximum bit
length is 864013. Hence `M=2^864013` is a strict bound and the chosen even
`kappa=864026` gives `2^kappa=8192M`. The eighteen distinct signed fixed
leaves match both their compressed/raw hashes and their exact native
recipes or fixed power-of-two definitions. The fixed binding authenticates
the final literal DAG hashes, not earlier intermediate versions.

The exact certificate replay tracks leading coefficients as polynomials in
the positive constants `lambda` and `threshold_scale`, rather than expanding
a billions-of-bits final coefficient. The exact source identities and the
independently proved source degree bound establish the cut-point leaders
`4lambda^(2E)`, `threshold_scale lambda^q`, and `32lambda^W`, including the
odd-threshold branch with its additional factor b. These proven leaders
seed the tail certificate, which obtains the claimed exact final degree
and nonzero leader without cancellation ambiguity in homogeneous source
intermediates. No native coefficient can change the source leaders.

The final positive-domain principal points are:

- width-174 regular/shared, simple majorant: 490 operations, degree 9,461,300;
- width-170 shifted/shared, quotient majorant: 564 operations, degree 4,400,764;
- width-170 packed/Horner, quotient majorant: 598 operations, degree 4,399,820.

The natural-domain forms use three more operations and have the same exact
degrees. The width-170 shifted `simple64` form uses 532 operations and
degree 5,370,068. Other checked comparison variants are retained in the
machine-readable metrics; no global optimality claim follows from this
finite search.

For completeness the inherited `support2048` degree claim was also audited
independently: its 687-term core defect has unique leading monomial
`2^30 A^17 C^18 i^6`, giving exact final degree
`158r+344n+4c+204` and diagonal leader
`2^172 kappa^4 rho^158 nu^344`.
