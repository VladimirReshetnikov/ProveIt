# Independent audit: exact height and minimum positive auxiliary completion

## Verdict and scope

**PASS: no mathematical defect found.** The audited core consists of the fresh
`HEIGHT.md` and `AUX_MINIMUM.md` in
`../square-product82-height-release-20261004/`, rebound to the recovered
Report45 proof. The exact height, both cubic formulas in Branch A, the Branch B
cubic, the least-radix choice with jumps preserved, and both auxiliary-minimum
theorems are valid. This audit adds the fixed-outer minimum-height corollary
below. No log-height transseries or inversion theorem is included or endorsed.

The original draft used a missing historical source path and obsolete
verification-status text. The fresh release repairs those issues. The recovered
proof is a newly authenticated text, not claimed byte-identical to the lost
proof. Its checked SHA256 is
`690c5a1dc237bd53a9582bfbe01fcd8a176174e6b116089a1842532f83c1770b`.
The original frozen chart source/proof/JSON pins are also checked independently.
`SOURCE_BINDINGS.json` pins the exact quantitative texts reviewed.

The 18-row table contains **11 exact bit lengths and 7 certified upper bounds**;
it does not claim all 18 rows are exact. Those bounds suffice for the exact
numerical maximum. Finite tests below corroborate the proof; they do not prove
its unbounded statements or instantiate a genuine compiler.

## Added corollary: the exact minimum height for a fixed outer tuple

Fix the compiler, ordinary input, and the 14 non-auxiliary supplied witnesses
from one Report45 construction. Allow arbitrary positive integers
`i,F_aux,U_aux,y_aux` that make the complete output zero. Let

    S0=Delta*c^2, H*=psi_S0(R),
    L=p+yexp+1, C=(p-1)L, N=(R-1)(2pL-1).

Then

    min max(all 18 supplied witnesses) = H*,
    2^N < H* < 2^(N+1),
    bl(H*) = N+1.

The minimum is attained by exactly the displayed auxiliary completion
`i=1`, `F_aux=Delta*c^4+1`, Pell index `m=R`, with its specified positive
`U_aux,y_aux`.

**Proof.** The varying-i theorem gives `y_aux>=H*`, strictly unless
`i=1,m=R`. The height theorem gives that the displayed `H*` strictly exceeds
every fixed outer witness and its own other three auxiliary witnesses. Thus
any completion has maximum at least `H*`, the displayed one attains `H*`, and
all others have maximum strictly larger. The finalizer forces the corresponding
`F_aux`, while the Pell sign and `U_aux` are uniquely determined, so no other
completion shares the minimum. This is a theorem for each fixed outer tuple,
not a lower bound for witnesses coming from different outer constructions.

## 1. Exact-length proof audit

For the actual family `p>=16`, `yexp>=3`, `R>=8`, `R<2p`, and `I<p`.
Put `X=2^p`, `Y=2^yexp`, and

    d=1/X+2/(XY), 0<d<2^(1-p), 2A=2^L(1+d).

For integer `0<=j<=4p^2`, the binomial/geometric estimate applies because
`j*d<8p^2/2^p<=1/32`. Consequently `(1+d)^j<32/31` for positive `j`;
zero exponents require only the non-strict lower endpoint. Every error exponent
used in the proof lies in this budget; in particular `2p(R-1)<4p^2`.

The Pell lower bound is strong enough to give strict dyadic lower endpoints:

    2^C<c<(32/31)2^C,
    2^(T-1)<S<(2^(T-1))(1+d)^(2p), T=2pL-1.

Because `S` is an integer, `2S-1>2^T`. Applying the Pell bounds at index `R`
then gives `2^N<y_aux<(32/31)2^N`, not merely an asymptotic estimate. For
`V=chi_S(R)/S`, successive chi ratios exceed `2S-1`; its norm gives
`V^2=(1-S^(-2))*y_aux^2+S^(-2)<y_aux^2`. Hence `V` has the same bit length,
while `V<y_aux`.

With `F0=4C+2L-2`, the strong witness satisfies
`2^F0<F_aux<(32/31)2^F0+1<2^(F0+1)`. For `U_aux`, division by `c` is
controlled on both sides before adding the remaining summands:

    2^(N-C)<V/c<(32/31)2^(N-C),
    N-F0=(2R-6)C+(2R-4)L-R+3>=R,
    R*F_aux+c<2^(N-1).

Thus `2^(N-C)<U_aux<(32/31+1/2)2^(N-C)<2^(N-C+1)`. In particular the
positive additive terms do not produce an unaccounted binary carry.

For the other rows:

* `h`: the resonance `(n-1)(p+2yexp+2)=C-yexp-1` is exact. The stronger
  elementary lower bound `psi_P(n)>M0^(n-1)+n` justifies subtracting `2n`
  before dividing by `E`; using only `k>2^(C-yexp)` would not suffice.
* `tau`: `n(p+2yexp+2)=pL` is exact; the chi lower endpoint and the same
  error budget give `2^(pL-1)<tau<2^(pL)`.
* `delta`: the step-two recurrence for `(psi_A(j)-j)/Delta` has the required
  inhomogeneous term `4j`. Its lower bound includes `I=3`, where `delta=4`
  exactly, and becomes strict afterward.
* `rho,sigma`: `g_2=1` and the inhomogeneous recurrence bound `g_j` between
  `(2A-1)^(j-2)` and `(2A+2)^(j-2)`. For `sigma`, the extra difference estimate
  `g_p-g_(p-1)>(2A-2)g_(p-1)>2^((p-2)L)` prevents a subtraction/carry gap.
* `i,s,w` have their stated immediate exact lengths. `J,F,alpha,t_tr,eta,zeta,Z`
  have valid one-sided bounds; all seven, and all other non-auxiliary rows,
  lie at or below `F0+1` bits. Since `N-F0>=R>=8`, they are strictly smaller
  than `y_aux`; `U_aux` is already smaller by its exact length.

This checks every row in the witness order and establishes numerical, rather
than merely asymptotic, dominance of `y_aux`.

## 2. Cubics, radix dependence, and jumps

Direct expansion of `(R-1)(2pL-1)+1` gives exactly

    A, epsilon=+1: (4R^3+4R^2-7R+2)/3,
    A, epsilon=-1: (4R^3-12R^2+9R+2)/3,
    B:            (25R^3+25R^2-39R+3)/14.

Their integrality follows from the source branch congruences. For all integer
`R>=100`, each lies strictly between `(5/4)R^3` and `2R^3`. The coefficients
`4/3` and `25/14` are therefore verified without substituting a rounded size
estimate into a bit length.

With `M=max(I,bl(K),61)` and genuine fixed `d=5^a`, the exact least choice is
`r=max(a,ceil(log_5(4M)))`, `t=5^r`. This is equivalently the integer procedure
of multiplying `5^a` by five until it first reaches `4M`; no floating-point
logarithm is needed. It gives `max(d,4M)<=t<=max(d,20M)`, strictly `t<20M`
when `t>d`. For example, `M=156` still permits `t=625`, whereas `M=157`
forces `t=3125` for `a=1`. These jumps cannot be replaced by a smooth fixed
multiple of the input.

The exact packed expansion

    R=q^4-q^3*F-q^2*(Z+1)+q*F+Z+M_mask

and `R<q^4` imply the stated positive relative error bound. Its use in the
asymptotic is legitimate even though the packing data vary with the input:
the error is uniform, and the branch is fixed by the compiler residue.
The strict `H8` lower bound uses integrality correctly: `bl(H)>2^(12t)`
implies `N=bl(H)-1>=2^(12t)`, then `H>2^N`. The remaining displayed
input bounds are valid monotone substitutions, and preserve the exact `t`
formula as the primary quantitative statement.

## 3. Auxiliary classification and both minima

The fundamental-unit descent is complete for integer-coordinate Pell
solutions. For `d=S^2-1`, a solution with `y>1` maps to
`(Sx-dy,Sy-x)` with positive first coordinate and `0<Sy-x<y`; a solution
with `y=1` is `(S,1)`. Hence every positive-y solution is a positive integer
power of `S+sqrt(d)`. No assumption about the full quadratic integer ring is
needed.

Modulo `S`, an even Pell index has chi congruent to `+1` or `-1`; it cannot
supply `SV`. At odd index `m`, the exact residue
`chi_S(m)/S=(-1)^((m-1)/2)*m (mod c)` applies since `c|S`. The actual
outer recurrence gives `8|c`, while `R=3 (mod4)`. Positive `V` is always
`1 (mod4)`; negative `V` is `3 (mod4)` and fails `V=-R (mod c)`.
The positive admissible indices are exactly `m=+R` or `-R (mod c)`.
The source bound `c>2R` then makes the least index `R`, with next index
`c-R`. This treats all signs, indices, and divisibility conditions.

Allowing every positive `i` introduces no missed negative-norm branch:
`P5=1` forces `Na*Qs=1`, and `4|S` makes `Na=y_aux^2 (mod4)`, excluding
`Na=-1`. Thus `Na=Qs=1` and necessarily `F_aux=Delta*i^2*c^4+1`.
The same sign and index classification remains valid. At fixed index
`m>=R>=3`, the binomial expansions of `psi_S(m)` and `chi_S(m)/S`
(for odd `m`) have nonnegative powers and coefficients, and a strictly
increasing term on `S>=2`. Together with strict growth in the Pell index
and `F_aux`'s strict growth in `i`, they uniquely minimize `y_aux,U_aux`
at `i=1,m=R`. `F_aux` is minimal for every admissible index at `i=1`;
the joint minimum of all four auxiliary coordinates is unique. This also
proves the corollary above.

## 4. New independent evidence

Only `check_independent.py`, newly written for this audit, was executed.
It imports only the Python standard library and never imports or evaluates
any upstream program or saved arithmetic graph. It uses explicit `need`
failures rather than Python assertions. Normal and `python -O` receipts are
byte-identical PASS results.

The checks include:

* Nine disjoint inner component fixtures: Branch A scales `u=4,...,11` and
  Branch B `v=2`, with 45 input-loader exponent checks, including `I=3`
* 37 separate transport/pure-power component cases
* 29 diagnostic outer CRT/packing fixtures, stopping at exponent data, with
  all non-dominant row-bound comparisons and the final double-exponential
  height envelope checked without constructing the associated witnesses
* 11,640 exact minimal-radix/envelope cases and an explicit radix jump test
* 5,703 cubic-envelope checks and 985 exact rational error-budget checks
* 69 Pell solutions found by independent exhaustive square tests for
  `2<=S<=20`, `1<=y<=5000`, each checked by descent and recurrence
* 45 auxiliary-sector cases over `8|c`, including both index residue classes,
  all signs, next admissible index, and strict positive-i comparisons
* Additional modulo-four and parameter-monotonicity checks

Diagnostic outer ports and inner component values are not genuine compiled
programs, and they are never combined into a genuine full tuple. The hard
Pell-coordinate cap is 450,000 bits; the receipt gives the attained maximum.
The checker also authenticates the recovered proof plus the three original
chart pins. The unbounded claims rest on the proof audit above.
