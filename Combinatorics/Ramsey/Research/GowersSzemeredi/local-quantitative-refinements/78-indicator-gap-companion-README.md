# Report290 exact companion

This standard-library-only Python 3.10+ companion supplies exact symbolic
certificates and bounded reproducible checks for **The Sharp Hereditary
Indicator Gap and Complete Endpoint Classification**. Run from the package root:

```sh
python -B companion/exact_checks.py
python -B tests/test_companion.py
python -O -B companion/exact_checks.py
```

The CLI has no computational options or input files. Unrecognized arguments
fail before any enumeration. Its deterministic JSON uses integers and reduced
rational strings, contains no timestamps, and is byte-identical under ordinary
Python and `python -O`. There are no dependencies, network calls, random seeds,
external executables, or writes. `-B` also suppresses interpreter bytecode caches.

The eight symbolic branch certificates cover arbitrary abelian targets by an
exhaustive coefficient-collision argument proved in the manuscript; they are
not finite-target map samples. The other enumerations are bounded diagnostics.
Neither component is a proof-assistant certificate. The general theorem also
requires the manuscript's exhaustive branch derivation, small-order histogram
arguments, and under-(P) classification, including its infinite-dimensional
gluing and limiting-box arguments. The sharp universal **indicator** bound is
19/27. No optimal universal **weighted** bound is claimed; an exact weighted
countercheck below distinguishes these statements.

## Conventions

All quadruples are ordered, including repetitions. The ordinary energy counts
`x+y=z+t`; respected energy additionally requires `a(x)+a(y)=a(z)+a(t)` in the
specified target group. Coordinates of finite cyclic factors are reduced
representatives. `Group((0,))` means the integers, whereas `Group((2,))` means
`C2`: these targets must not be interchanged.

Every enumerated map is normalized by `a(0)=0`. Subtracting a constant from all
values preserves every target-sum equality, every energy, condition (P), and
the structural class. This is an exhaustive normalization within each finite
range, not a sample of maps. Cartesian-product element order is lexicographic.

## Reusable API

Import `from companion import exact_checks as e` from the package root.

- `Group(moduli)`: immutable product of one to four cyclic factors; `0` denotes
  an infinite integer factor. `zero`, `finite`, `point`, `add`, `sub`, `scale`,
  and `elements` provide checked coordinate operations. `elements()` refuses
  infinite groups. Finite factors of order one are permitted
- `Energy(ordinary, respected)`: exact record with reduced `ratio`; requires
  `ordinary>0` and `0<=respected<=ordinary`
- `energy(domain, target, weights, images)`: exact pair-sum histograms, with
  rational nonnegative weights. `images` must cover exactly the positive
  support after zero weights are removed
- `direct_energy(...)`: independent literal four-loop weighted oracle, on at
  most eight positive support points
- `derivative_masses(domain, target, images)`: `Q_h` for every domain element
  of a full finite map. Their sum is its full-indicator respected energy
- `indicator_minimum(domain, target, images)`: every nonempty subset of a full
  domain of order at most eight. Returns the exact minimum, a deterministic
  witness, subset count, and minima by size. This computes only the indicator
  infimum on that finite domain, not the weighted infimum
- `condition_p(domain, target, images)`: checks every pair `(x,h)` for
  `a(x+3h)+a(x)=a(x+2h)+a(x+h)`. Returns `holds` and a first failing witness
- `classify_finite(domain, target, images)`: returns `kind` equal to `affine`,
  `index_two`, or `other`, with the canonical translation subgroup and its
  common homomorphism. The target may have integer factors. This classifies
  structure without claiming to compute the infimum of a general map
- `plane_data(target, values)`: four values, in `00,01,10,11` order, give
  respected energy, doubled-value squared mass `D`, and number `k` of respected
  opposite-pair partitions. The returned formula is `D+24+8k`
- `affine_planes(domain)`: distinct four-point affine planes of an
  elementary-two domain, without repetitions; dimensions one through four
- `grid_obstruction(domain, target, images, h, k)`: the exact target element
  `a(2h+k)-a(k)-a(2h)+a(0)` for a full finite map
- `obstruction_average(q)`: exact reciprocal average for `q=2` or `q=4`
- `box_energy(rank, torsion_order, n)`: evaluates the exact prescribed-box
  formula, without enumerating a box
- `box_quotient_counts(n)`: literal ordered counts for
  `[-n,n] x C4 -> C2 x C2` and `b(p,q)=pq in C2`. Returns all 64 additive
  quotient-pattern lift counts, four quotient-difference counts, energy, and
  relative maximum-minus-minimum pattern spread. Zero counts are retained
- `branch_data(row)`: immutable coefficient vector and test subset for rows
  1 through 8 of the exhaustive extension argument
- `coefficient_histogram(coefficients, subset, modulus=None, method="pairs")`:
  the signed defect histogram `C(z,t)`. `None` means integer-sum equality;
  moduli 10 through 18 retain wrapping. The independently implemented
  `method="quadruples"` literally loops over all ordered quadruples
- `three_case_maximum(histogram)`: primary arbitrary-target certificate using
  orders 2, 3, and at least 4/infinite. It checks the zero-wrap and support-
  diameter hypotheses before evaluating the three possible upper numerators
- `symbolic_numerator(histogram, q, h)`: tests `t+z*h=0 mod q`; `q=None`
  denotes infinite order, hence integer equality. Nonzero `u` excludes `q=1`
- `symbolic_maximum(histogram)`: independently enumerates the complete finite
  symbolic range `h=-M..M`, `q=2..2M` plus infinity, with `M=max|t|`
- `realized_pair_energy(coefficients, subset, modulus, q, h)`: independent
  pair-sum energy in `C_(Nq)` with `u=N,d=h`, or in `Z` for infinite order.
  It retains `N*d=h*u` and realizes the formal collision pattern. This is
  attainment across allowed targets, not a claim that every pattern can be
  attained in an already fixed target
- `branch_certificate(row, modulus=None)`: cross-checks independent defect
  counts, both arbitrary-target bounds, the exact listed positive-wrap
  polynomial, the listed ratio, and an explicit target realization
- `check_symbolic_certificates()`: all eight no-wrap and 72 finite-wrap cases
- `check_c3_sharp_indicator()`: all seven subsets for `C3 -> Z`, plus an exact
  rational weighted test below 19/27
- `check_small_order_arithmetic()`: integer inequalities from the arbitrary-
  target order-7/8/9 proofs; the paper proves their histogram hypotheses
- `run_checks()`: all fixed diagnostic ranges below, as an exact Python record
- `jsonable(record)`: serializes companion records. Fractions become reduced
  strings; dictionaries with non-string keys become sorted key/value records

Methods and functions beginning with `_` are unchecked or specialized internal
helpers, not a public input interface. In particular, private group arithmetic
is used after validation and does not repeatedly check coordinate bounds.
Public arithmetic validates its inputs. An output outside the input bound
cannot be passed to another checked public operation; internal calculations
retain such derived coordinates exactly.

### Canonical kernel and division-free verification

For a full map, normalize `b(x)=a(x)-a(0)` and compute

`K = {h: b(x+h)-b(x)=b(h) for every x}`.

The classifier explicitly checks subgroup closure and the homomorphism law on
`K`. If `K=G`, the map is affine. If `[G:K]=2`, choose the first point `t`
outside `K`, put `u=b(t)`, and check the same homomorphism on the other coset.
The nonzero defect is `eta=2u-b(2t)`; no division or extension of the kernel
homomorphism into the original target is used. It additionally verifies

`K = {x: a(2x)-2a(x)+a(0)=0}`

and that the curvature is exactly `-eta` on the complement. This is a finite
check of the intrinsic kernel and its uniqueness for endpoint maps. The test
suite also verifies the example `C4 -> C2`, `a(j)=floor(j/2)`, where the common
homomorphism on `K={0,2}` does not extend to a homomorphism `C4 -> C2`.

## Hard bounds and invalid inputs

All input-limit failures raise `ValueError`; failed diagnostic invariants raise
`RuntimeError`. These are explicit checks and remain active under `python -O`.
There are no `assert` statements in the companion.

- A group has one to four factors, each finite modulus at most 128; the product
  of finite-factor orders is at most 128, also when integer factors occur
- Group coordinates are exact `int` values, never booleans; integer coordinates
  lie in `[-4096,4096]`, finite coordinates in `[0,m-1]`. Public integer
  multipliers lie in `[-4096,4096]`
- Public maps and weights are plain dictionaries, not custom mapping objects;
  coordinate containers and moduli are tuples of the exact required lengths
- Energy input dictionaries have at most 128 keys. Nonnegative weights are
  exact `int` or `fractions.Fraction`, with numerator bit length at most 128
  and denominator bit length at most 64. Floats, booleans, negative values,
  all-zero support, extra image keys, and noncanonical coordinates are rejected
- Literal four-loop energies and exhaustive subset minima have an eight-point
  bound. Full-map classification, (P), and derivatives have at most 128 domain
  elements because their domains must be finite supported `Group` objects
- The internal normalized-map enumerator has order at most eight, target order
  at most nine, and at most 150,000 maps per call. The CLI's aggregate cyclic
  range contains 138,516 maps; callers cannot expand its range through flags
- Literal box-pattern enumeration allows radii 0 through 8, hence at most
  68 points. The formula-only box-energy helper allows rank 0 through 4,
  torsion order 1 through 128, and radius 0 through 32
- The obstruction-average helper accepts only exact orders 2 and 4
- Symbolic coefficient vectors and test subsets are exact tuples of one through
  ten entries. Coefficients lie in 0 through 3; test indices are distinct,
  increasing, and within the vector. A finite certificate modulus is exactly
  an integer from 10 through 18; `None` means no wrapping. Thus literal
  quadruple certificates require at most 10,000 iterations
- Defect dictionaries have at most 39 entries, integer `z` in -1 through 1,
  integer `t` in -6 through 6, positive integer counts, total at most 10,000,
  a diagonal term, and explicit `(z,t) <-> (-z,-t)` symmetry
- `symbolic_numerator` accepts `q=None` or integer orders 2 through 4096, and
  integer `h` in `[-M,M]`. `symbolic_maximum` uses only orders 2 through `2M`
  plus infinity. The realization helper permits `h` in -6 through 6 and
  computes pair residues without enumerating `C_(Nq)`
- Boolean rows, orders, coefficients, moduli, counts, and slopes are rejected
  before counting, as are invalid methods, duplicate indices, overlarge
  vectors, and unsupported three-case diameter hypotheses

These limits bound the actual loops before enumeration begins. They are
computational-interface limits, not limitations of the mathematical theorem.

## Fixed diagnostic ranges and outcomes

### Direct energies

27 rational-weight cases compare pair-sum histograms with literal ordered
quadruples, on four-point supports in `Z`, `C4`, and `C2 x C2`, with targets
`Z`, `C3`, and `C2 x C2`. Tests additionally compare independent modular
integer counts, derivative masses, repeated-coordinate contributions, and
fourth-power scaling of weights.

### Small cyclic groups

All 138,516 normalized maps `C_n -> C_m` for `1<=n<=6`, `2<=m<=9` are checked.
There are 222 maps satisfying the unit-direction form of (P); every such map
passes the generic canonical-kernel structural classifier. The remaining maps
have the following largest observed full-indicator ratios:

| Domain | Normalized maps | Outside (P) | Largest ratio outside (P) |
|---|---:|---:|---:|
| C1 | 8 | 0 | not applicable |
| C2 | 44 | 0 | not applicable |
| C3 | 284 | 270 | 19/27 |
| C4 | 2,024 | 1,960 | 11/16 |
| C5 | 15,332 | 15,320 | 17/25 |
| C6 | 120,824 | 120,744 | 19/27 |

For every nonaffine `C5` case, both implications `Q1=17 => Q2=13` and
`Q2=17 => Q1=13` are checked. These finite target ranges supplement the
arbitrary-target derivative-partition argument in the manuscript.

### Elementary-two planes and gluing

All 1,871 normalized four-point maps into `C2` through `C8`, `C2 x C2`, and
`C2 x C4` are checked. For each map, all 64 additive ordered quadruples are
counted independently; their count agrees with `D+24+8k`. Every plane has
energy 64, energy 48, or energy at most 40. Every 64/48 case is also passed to
the generic structural classifier.

On `F2^3`, all 35,083 normalized maps into the four targets below are checked.
All fourteen affine planes are available; the search stops at the first bad
plane, if present. If none is bad, the generic classifier verifies global
structure rather than inferring it from the absence of a local witness.

| Target | Maps | Affine | Nonaffine index two | Has bad plane |
|---|---:|---:|---:|---:|
| C2 | 128 | 8 | 0 | 120 |
| C3 | 2,187 | 1 | 14 | 2,172 |
| C4 | 16,384 | 8 | 56 | 16,320 |
| C2 x C2 | 16,384 | 64 | 0 | 16,320 |

The tests independently classify another 365 normalized maps by exhaustively
searching homomorphisms to `C2`, without using the translation-subgroup method.

### Mixed-coordinate finite classification

All 1,299 normalized maps `C2 x C3 -> C_m`, `m=2,3,4`, are classified,
tested for (P), and checked by full energies. Their full energies are independently
calculated with derivative histograms. Affine and nonaffine index-two maps
have full-indicator ratios 1 and 3/4, respectively; all other maps in this
specific range have full-indicator ratio at most 19/27. This last finite
observation is not asserted for every arbitrary map's full indicator. The tests
include `C16 -> C2`, equal to 1 only at zero: its full-indicator ratio is
`407/512 > 3/4` although the map is in the third class. The four-point subgroup
`{0,4,8,12}` has ratio `5/8`. Thus high energy of a single full indicator must
not be substituted for the hereditary hypothesis.

### Genuine order-four obstruction

For `i=2m+epsilon`, `j=2n+delta`, use

`a(i,j)=m*delta-n*epsilon+2*m*n (mod 4)`

on `C8 x C8`. All 4,096 pairs `(x,h)` satisfy (P). The obstruction for the two
coordinate generators is `s=1 in C4`. Pair-sum and derivative-histogram
energies agree: ordinary 262,144, respected 71,680, ratio `35/128`.
The classifier confirms that the map is outside both endpoint families.
All sixteen quotient-difference-class bounds are checked, along with the
reciprocal averages `5/8` for order two and `11/32` for order four. Tests verify
eight-periodicity and both signed derivative identities at negative as well
as nonnegative integer grid coordinates.

### Prescribed box pattern counts

For `L=Z x C4`, quotient `C2 x C2`, and `b(p,q)=pq in C2`, literal box counts
at radii 1, 2, 4, 8 have respectively ratios

`13/19, 11/17, 103/163, 121/193`.

Their ordinary energies are 1,216; 5,440; 31,296; 209,984. Every one of the
64 additive quotient patterns is present at these radii. Minimum/maximum
pattern lift counts are `(8,48)`, `(48,152)`, `(352,680)`, `(2752,3912)`.
The JSON also gives exact relative spreads and four quotient-difference
counts. The algebraic proof establishes the limiting ratio 5/8; these bounded
values only illustrate and cross-check it.

### Order-five integer example

For `a(j)=j` from `C5` to `Z`, all 31 nonempty subsets are evaluated. Minimum
ratios at subset sizes 1 through 5 are

`1, 1, 15/19, 9/13, 17/25`.

Thus the example's finite indicator infimum is exactly 17/25. Its derivative
squared masses are `25,17,13,13,17`; no weighted infimum is asserted.

## Arbitrary-target symbolic proof certificates

These are an exhaustive symbolic coefficient calculation, not a bounded search
of maps into selected finite targets. The manuscript derives eight possible
extension branches, with `b_i=c_i*u`, `u!=0`, on at most ten distinct indices.
The test sets and coefficient vectors are the immutable `BRANCH_ROWS` inputs.
Every histogram is generated twice: by pair-sum convolution and by a separate
literal four-loop ordered-quadruple count. Both implementations must agree.

### No wrapping

The signed zero-wrap data `(D0,D1=D-1,D2=D-2)` are exactly

`(53,14,2), (98,24,0), (90,20,0), (98,24,0),`
`(204,64,6), (321,84,0), (139,36,0), (470,100,0)`.

There are no other zero-wrap coefficients. A nonzero `u` can cancel defects
`2u` only at order two; it cannot cancel `u`. The eight upper ratios are

`57/85, 49/73, 9/13, 49/73, 27/43, 107/163, 139/211, 47/67`.

The largest is `47/67 < 19/27`. These integer-sum counts apply unchanged when
the cyclic order is at least 19, since all index sums lie between 0 and 18,
and to infinite cyclic directions.

### Wrapping with the original slope retained

For `N=10,...,18`, write the original values as `a_i=beta+i*d+c_i*u` and put
`v=N*d`. The counted target defect is `z*v+t*u`, not just `t*u`. Here
`z=(i+j-k-l)/N` belongs to `{-1,0,1}`. Subtracting `i*d` is only an integer-
representative normalization; it is not assumed to descend to `C_N`.

The primary certificate writes the positive-wrap polynomial
`P_N(X)=sum_t C_N(1,t)*X^t`. The code lists and asserts all 31 nonzero
polynomials; the other 41 are explicitly verified zero. Every polynomial has
support diameter at most three. Therefore all arbitrary abelian targets are
exhausted by these three coefficient-collision cases:

1. `ord(u)=2`: same-parity exponents can merge, with largest class mass `W2`
2. `ord(u)=3`: equal residues modulo three can merge, with largest mass `W3`
3. `ord(u)>=4` or infinite: distinct exponents cannot merge; let `Winf` be
   the largest individual coefficient

With empty-polynomial masses zero, the exact universal upper numerator is

`max(D0+2*D2+2*W2, D0+2*W3, D0+2*Winf)`

and the ordinary denominator is `D0+2*D1+2*D2+2*P_N(1)`. When `v` is outside
`<u>`, no nonzero-wrap comparison is respected, so this bound still applies.
The code separately checks that case. No cyclicity or finiteness of the
original target is needed: all relevant collisions occur among multiples of
its single nonzero element `u`.

### Independent finite q/h reduction and target realization

Let `M=max|t|` over the full histogram. If any wrap is respected, then `v=h*u`
for some `h` in `[-M,M]`. If `q=ord(u)`, respectedness is exactly
`t+z*h=0 mod q`, or equality for `q=infinity`. Since `|t+z*h|<=2M`, every
order larger than `2M` has exactly the infinite-order zero pattern. Thus
`q=2,...,2M,infinity` and `h=-M,...,M` are an exhaustive symbolic range.
The implementation uses exactly these endpoints and independently recovers
all 72 three-case maxima. Tests compare every q/h pattern to pair energies,
and explicitly check orders `2M+1`, `2M+2`, and 4096 against infinity.

Every maximizing formal pattern has an independent realization across allowed
targets: take `u=N`, `d=h` in `C_(Nq)`, or in `Z` for infinite order. Then
`ord(u)=q`, `N*d=h*u`, and independent pair histograms attain the computed
ratio. This does not assert that the same value is attainable inside an
arbitrarily preassigned target.

The largest of the 72 wrap ratios is `59/84`, strictly below `19/27` because
`59*27=1593 < 1596=19*84`. The deterministic JSON, schema version 2, contains
all full signed histograms, polynomial coefficients, three numerator cases,
finite-reduction maxima, and attaining q/h parameters.

### Small orders and indicator sharpness

The order-7/8/9 helper checks the exact arithmetic of the manuscript's
arbitrary-target histogram cases, including the arithmetic-cut ratios
`33/49`, `43/64`, and `163/243`. The resulting bounds are `33/49`, `11/16`,
and `19/27`. This helper does not replace the algebraic cycle, involution,
and repeated-histogram arguments in Section 3.4.2.

For `a:C3 -> Z`, `a(j)=j`, every proper nonempty subset has ratio 1 and the
full set has ordinary energy 27 and respected energy 19. Both count oracles
check all seven subsets, establishing the example's exact indicator infimum
`19/27`. In contrast, exact weights `(1,2/3,1)` have ratio `467/683 < 19/27`.
This provides a rational check of the weighted distinction without claiming
that these weights minimize the weighted ratio. The manuscript's sharpness
claim is for the universal indicator threshold only.

## Test and runtime scope

The 48 tests check API validation, numerical hard limits, independent
classification, exact counting, the nonextendable kernel example, curvature
uniqueness, grid signs and negative indices, box counts, declared enumeration
counts, all symbolic coefficient certificates, exact target realizations,
sharp C3 indicator subsets, unknown CLI arguments, and optimized execution. The test suite runs
the full CLI in both ordinary and optimized modes and compares output bytes.
At preparation, the full diagnostic took about 2.4 seconds and all 48 tests
about 6.0 seconds in the supplied environment; timings are descriptive and
are not embedded in deterministic output. Each test-suite CLI subprocess has
a 45-second timeout. These finite runtimes are not universal machine guarantees.
