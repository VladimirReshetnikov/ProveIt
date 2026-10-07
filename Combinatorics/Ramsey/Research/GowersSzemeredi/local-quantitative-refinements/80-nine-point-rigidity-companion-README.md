# Exact companion to Report292

This small, fresh implementation uses only the Python standard library. It
reconstructs its own finite geometry, ordered additive quadruples, pair
convolutions, and integer-relation certificates. It requires Python 3.10 or later.
No installation, network access, input files, or external mathematics software is
needed. It reads no report data and writes no files.

From the report directory:

```
python -I -B -X int_max_str_digits=640 companion/exact_checks.py
python -I -B -X int_max_str_digits=640 tests/test_companion.py
python -I -O -B -X int_max_str_digits=640 companion/exact_checks.py
python -I -O -B -X int_max_str_digits=640 tests/test_companion.py
```

The checker accepts no arguments, emits deterministic exact JSON on standard
output, and exits unsuccessfully if any certificate fails. Redirect its output
to a separate directory if a saved receipt is desired. The two checker modes
produce identical standard output. All mathematical guards use explicit
exceptions rather than Python `assert` statements.

## Coverage

- Three-point line energy `15 + 4m`, with ordinary energy 27, and the equivalence
  between a midpoint equality and repeated cyclic increments: 2,150 exact cases
  over bounded integer values and cyclic targets of orders 1 through 9
- All 30 integer partitions of nine. The nonconstant partitions with square
  sum above 45 are `(8,1)`, `(7,2)`, and `(7,1,1)`. For every compatible arrangement
  in three cycles, explicit integer combinations of the zero-cycle relations
  either force distinct colors equal or certify the surviving `(7,2)` pattern:
  `3v=0` and `2(u-v)=0`. A C2 realization verifies that the surviving profile is
  consistent. Thus this small algebraic certificate does not divide in a target
  group or assume the absence of torsion
- The order-two spike: six-point energies 162 and 106, ratio `53/81`; full-plane
  energies 729 and 505, ratio `505/729`. Giving the spike weight `8/5` and
  the other five support points weight one gives ordinary energy `149121/625`
  and respected energy `93121/625`, with ratio strictly below `5/8`. The exact
  polynomials in the spike weight are `(81,56,24,0,1)` and `(81,0,24,0,1)`.
  The reduced ratio is `eta=13303/21303`. Scaling by five gives six positive
  integer weights from `{5,8}`, with energies 149121 and 93121. This is one
  explicit weighted upper-bound witness, not an optimality claim
- A target-independent two-row certificate using formal row constants `b,c`
  and a nonzero order-two symbol `delta`. Every source sum has just one pair
  of coefficients of `b,c`, so additional relations among the row constants
  cannot affect the indicator count or weighted polynomials
- An independent reconstruction of formulas (A)-(D) and the complete
  single-spike sharpness table below, checking all 511 supports and precisely
  eight minimizing supports
- The exact chain `5/9 < 49/81 < eta < 5/8 < 53/81`, together with the stationary
  relation `t^4+8t^2-27=0` for the optimized six-point witness and exact rational
  brackets for its positive root. The low-histogram full-plane bound is
  `441/729=49/81`
- All 512 C2-valued maps and all 511 nonempty indicator supports for each map,
  totaling 261,632 map/support pairs. There are 2 constants, 24 translated cuts,
  and 486 outside maps. The outside maximum full-indicator ratio is `505/729`;
  the outside maximum of the minimum over indicators is `53/81`
- All `26^3 = 17,576` choices of allowed sections on three fixed parallel planes
  in F3^3, testing the other plane-section conditions as needed. Exactly 80
  subsets survive: empty, full, 39 affine hyperplanes, and their 39 complements
- Exact coefficients in ascending powers of tau for weights `(1,tau,1)` on C3:
  ordinary `(6,8,12,0,1)` and respected `(6,0,12,0,1)` for targets Z, C2, C4, C6,
  and C9. The affine C3 target has equal polynomials. Exact rational checks also
  record the minimizer's polynomial, a positive-root bracket, and the threshold
  difference `17/25 - 53/81 = 52/2025`
- For the explicit cut `a(x,y)=y` into Z, with representatives `y=0,1,2`, all
  511 indicators have minimum ratio `13/19`. Exactly three supports attain it:
  the full plane with one point from the middle fiber removed. Each has ordinary
  energy 456 and respected energy 312. The full-plane ratio is `19/27`

The C2 calculation groups ordered quadruples by their exact support and the
parity mask of their point multiplicities, then applies a nine-bit subset-sum
transform. Full-plane pair convolution independently checks all 512 maps.
Six representative maps receive additional independent target-arithmetic and
pair-convolution checks on every support. All 511 integer-cut supports also
receive pair-convolution crosschecks.

## Analytic single-spike certificate

For the C2 map that is one at the origin and zero elsewhere, a support avoiding
zero has ratio one. For a support S containing zero, write n=|S|, let L be the
number of complete affine lines in S, and let l count those through zero.
Let N_s count ordered pairs of S summing to s, and put
T=sum over s in S\{0} of (N_s-2). The checker derives all these quantities from
point sets and pair sums and independently checks:

- (A) E = 2n^2-n + 8 binom(n,4) + (36-8n)L
- (B) E-E_a = 4T
- (C) T = 2[binom(n-1,3)-(n-5)l-L]
- (D) L = 12-4c+binom(c,2)-L_C and l = 4-c+p_C, where C is the complement,
  c=|C|, L_C counts its complete lines, and p_C its antipodal pairs

Each formula is checked on all 256 supports containing the origin. The receipt
includes the number of supports of each displayed type.

| n | Possible (E,T) | Minimum indicator ratio |
|---|---|---|
| 1 | (1,0) | 1 |
| 2 | (6,0) | 1 |
| 3 | (15,0), (27,2) | 19/27 |
| 4 | (36,2), (40,0), (40,2) | 7/9 |
| 5 | (77,4), (81,6) | 19/27 |
| 6 | (150,10), (150,12), (162,14) | 53/81 |
| 7 | (271,18), (271,22) | 183/271 |
| 8 | (456,36) | 13/19 |
| 9 | (729,56) | 505/729 |

The eight equality supports are exactly the complements of the affine lines
avoiding the origin. This certificate concerns one explicit map and establishes
its indicator minimum; universality is supplied by the report's algebraic proof.

For the optimized six-point weighted witness, let N(t)=81+24t^2+t^4. The checker
verifies `tN'(t)-N(t)=3(t^4+8t^2-27)` and reduces N modulo this stationary relation
to `108+16t^2`. At `t^2=sqrt(43)-4` this gives the report's gamma expression.
Exact rational checks bracket the positive root between `3/2` and `8/5`, and
verify the substitution giving `gamma > 93/149 > 49/81`. The proof supplies the
monotonicity and minimization argument; no floating-point approximation is used.

## Interpretation and limits

These are bounded diagnostics and exact finite certificates. The arbitrary-target
plane theorem and the infinite-dimensional gluing theorem are proved in the
report, not inferred from the enumerations. The separate index-three energy
argument supplies the universal lower bound and exact weighted value rho.
Indicator minima are not weighted infima; in particular the explicit `13/19`
example must not be presented as a value of rho. The sharp indicator
constant is `53/81`. The constants gamma and eta are weighted upper bounds with
no weighted sharpness claim; the strict weighted threshold `5/8` yields the same
family classification by the report's argument.

## Small public API and input bounds

`energy(rank, values, weights, modulus=None, method='pairs')` returns an immutable
`Energy(ordinary, respected)` with an exact Fraction-valued `ratio` property.
The domain is F3^rank in lexicographic coordinate order, available from
`points(rank)`. Supported ranks are 0 through 3, so the largest domain has 27
points. `values` and `weights` must be full-domain tuples. Target values must be
integers in `[-4096,4096]`; `modulus=None` means Z and integer moduli 1 through
4096 mean cyclic targets. Input weights are nonnegative integers or Fractions,
not all zero, with absolute numerator and denominator at most `2^31-1`.
No float or bool substitutes are accepted. `method='triples'` selects an
independent direct source-triple implementation.

`indicator_energy` replaces `weights` by a nonempty strictly increasing tuple
of point indices. `support_weights` exposes that conversion. `integer_partitions`
is restricted to totals 1 through 9. `cut_polynomials` accepts the same target
modulus choices as `energy`. Functions whose names begin with an underscore are
private fixed-size implementation helpers rather than public input interfaces.
The JSON coefficient arrays use ascending powers; rational numbers are encoded
as exact strings. Bit `i` in a support or coloring mask refers to point `i` in
lexicographic order.
