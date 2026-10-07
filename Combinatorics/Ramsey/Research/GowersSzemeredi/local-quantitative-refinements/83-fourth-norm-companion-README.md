# Exact companion to Report295

This is a standalone, read-only Python 3.10+ standard-library companion. No
installation, network, earlier report, research directory, computer algebra
system, numerical optimizer, or floating-point arithmetic is needed. The
release was tested with Python 3.12.

From the report directory:

```sh
python -I -B companion/exact_checks.py
python -I -B tests/test_companion.py
python -I -O -B companion/exact_checks.py
python -I -O -B tests/test_companion.py
```

The checker accepts no configuration or positional arguments. It reads the
adjacent `interval_certificate.json`, independently regenerates its contents,
and prints one canonical JSON receipt to stdout. It creates or changes no
files. Normal and optimized receipts are byte-identical, independent of the
working directory, and contain no timestamps, paths, or platform details.
Mathematical guards raise explicit exceptions; none uses Python `assert`.

Public source inventory:

- `companion/__init__.py`
- `companion/exact_checks.py`
- `companion/interval_certificate.json`
- `companion/README.md`
- `tests/test_companion.py`

## What the code does and does not establish

The paper proves the all-parameter two-value theorem, its equality statements,
the finite stationary-root reduction, the constant transition, the all-order
reflection formula and candidate rule, and the finite-group spectral saturation
results. This program checks their algebra and the explicitly labeled finite
examples. No finite experiment is promoted into an all-order or all-group
proof. The program is not a formal proof-assistant verification.

In particular, no general arbitrary-gamma quintic norm solver is implemented.
The complete formal stationary-polynomial identity is checked for symbolic
parameters, while the paper supplies the exact finite reduction to real roots
of degree-at-most-five polynomials and the constant candidate. This distinction
also applies to the balanced branch, degenerate parameters, and all-equality
classification.

## Complete formal polynomial checks

There are 54 identities. A sparse polynomial is its complete mapping from
sorted monomials to exact rational coefficients; equality compares every
coefficient. No interpolation, random sampling, parameter grid, or external
symbolic engine is used.

The checks include:

- The fixed-mean quartic and its stationary cubic; the Vieta coefficients and
  the final three-singleton contradiction factor
- All three root curvatures, the sum-zero tangent, the exact Hessian second
  variation after clearing positive multiplicity denominators, and its sign
  decomposition
- The strict-norm directional derivative, all five integer two-point moments,
  and the normalized fourth-moment relation
- Independently binomial-generated numerator and denominator, every stationary
  quintic coefficient, centering and reflection specializations, the identically
  zero balanced reflection branch, and all balanced stationary branches
- The normalized mean-one gap, integer-coordinate constant gap, discriminant,
  strict split maximum, reciprocal-symmetric threshold, threshold derivative,
  threshold polynomial and extremal discriminant, transition below n, radical
  parameter identities, and exact completion of the quadratic square
- Reflection scalar stationarity, the critical denominator, G derivative and
  continuous maximum, moment simplification, and the beta conversion
- The complex phase-average coefficient and the nine-point radical identity
  in Q[sqrt(6)]
- The group-independent point-spike energy expansion, parity relation,
  stationary numerator, radical stationary relation, and positivity polynomial

The analytic uses of positivity, compactness, Lagrange multipliers, phase
averaging, uniqueness, and equality classification remain in the paper.

## Exact radical intervals and multiplicity decisions

For a nonnegative rational a/b and S=10^65, the program computes

```
t = isqrt((a*S*S)//b)
```

and checks the integer inequalities

```
t*t*b <= a*S*S < (t+1)*(t+1)*b.
```

Thus sqrt(a/b) lies between t/S and (t+1)/S, with a point interval when the
left equality holds. All subsequent interval operations use exact Fractions;
reciprocals reject any interval containing zero. Square roots are enclosed
endpointwise. Final 40-place decimal endpoints are rounded outward by integer
division and checked against the underlying exact rational intervals. Every
printed decimal endpoint is an exact terminating-decimal rational.

The candidate rule computes the floor and ceiling of
n(1-sqrt(2/3))/2 using rational enclosures, then clips to 1..floor(n/2).
A floor is accepted only if both enclosing rationals have the same floor.
Comparisons use k squared, avoiding an unnecessary nested radical. A winning
candidate must have lower bound strictly greater than every other candidate's
upper bound. Overlap or a tie raises an explicit unresolved-comparison error;
the code never guesses or silently discards a tie. The paper's general formula
retains all ties. The public helper is bounded to 1 <= n <= 1,000,000; its
precision and explicit failure behavior are implementation limits, not limits
on the mathematical theorem.

The bundled certificate records:

- Reflection values for n=1,2,3,4,8,9,10,11,12,13,14,15,16,27,81
- Every candidate's y, k squared, k, fourth-power norm, norm, and beta
- Positive winner-minus-loser k intervals for n=11 through 16
- The unique winners m27=3 and m81=7, and the positive beta27-minus-beta81 gap
- Constant-transition intervals for n=3,9,30

The n=1,2 reflections are handled separately and have norm one. A balanced
split contributes exactly k=0 and norm one. The switch is m=1 through n=15
and m=2 at n=16. Further supplemental exhaustive comparisons of every allowed
multiplicity for n=3..100 agree with the two-candidate rule; these are checks,
not its proof.

The exact equalities C16=C8 and C27=C9 (and beta27=beta9) are verified by
rational identities for repeated split proportions and their radical inputs.
They are not inferred from overlapping intervals. The n=4 value k squared=9/25
and C4=4 is checked exactly. The nine-point radical simplification is a formal
identity modulo z squared=6, not a decimal coincidence.

## Supplemental finite character and energy examples

All character computations use integer polynomial coefficients in
Q[z]/(z^(2c/3)+z^(c/3)+1), where c is 3,9,27, or 81. There are no approximate
complex roots of unity. The code verifies character orthogonality and

```
sum_(chi in L annihilator) chi(x) = |L annihilator| * 1_L(x)
```

coefficientwise for an explicit subgroup L of order nine in each of the three
abelian group types of order 27 and five group types of order 81:

```
C27, C9 x C3, C3^3
C81, C27 x C3, C9 x C9, C9 x C3 x C3, C3^4.
```

Ordered-pair convolution independently constructs ordinary, retained, and
signed energies for weight t at zero, one on L minus zero, and zero outside L.
In every example it gives, as exact polynomials,

```
E  = t^4 + 48t^2 + 224t + 456
Ea = t^4 + 48t^2 + 456
Es = t^4 + 48t^2 - 224t + 456
2Ea = E + Es.
```

A direct nonsplit quotient example C27 -> C9, with kernel {0,9,18}, verifies
that the constant-fiber lifted energies are exactly 3^3 times these polynomials.
It does not assume the extension splits.

The code additionally checks all 256 identity-containing character subsets on
C3^2. Exactly six have everywhere nonnegative real character sum, and these
are exactly the six subgroups, tested independently by addition closure. This
is a finite illustration of the character-sum lemma, not its general proof.

The order 27 and order 81 interval arithmetic and character algebra support the
paper's examples. The general classification of spectral saturation and the
compactness argument for strictness come from the paper. No exact minimum of
the nonsaturating order 81 point-spike problem is computed or asserted here.
Nor does the companion classify all equality weights for nontrivial fibers.

## Validation and adversarial tests

All exact scalar interfaces reject booleans, floats, strings, and unsupported
number types. Integers and rational components are bounded to 16,384 bits.
Polynomial input permits at most 12,000 terms, 32 variables, degree 32, and
24-character identifier names; multiplication has a two-million-pair budget.
The public coefficient mapping is immutable. Formal substitution and
coefficient extraction never sample variable values.

Square-root precision must be 1..100 decimal places. Intervals are immutable
and reject reversed bounds and negative square-root domains. Finite character
helpers support only the documented power-of-three conductors and groups of
order at most 81. Energy examples require exactly one formal weight per point.
These finite helper bounds do not constrain any theorem.

The certificate loader reads at most 100,001 bytes, rejects files over 100,000
bytes, and checks ASCII JSON with depth at most 16, no duplicate keys, no
floating/nonfinite numbers, and bounded integer tokens. It requires canonical
encoding. Validation compares canonical bytes against freshly regenerated
exact enclosures, so missing fields, extra fields, false endpoints, changed
winners, and booleans replacing integers are rejected.

The 50 tests cover the above boundary and mutation cases, a polynomial that
vanishes on a sample grid but is not an identity, deliberately changed quintic
coefficients, independent rational C3 triple-energy enumeration, unresolved
candidate comparisons, balanced/low-order branches, false certificates,
unknown CLI options, missing files, normal/optimized byte equality, and an
arbitrary working directory. A subprocess audit hook denies any attempted
write, network access, or process launch while the checker runs from a
read-only copy; source and certificate hashes remain unchanged.

## Provenance and independence

The sparse rational Polynomial representation and input-validation patterns
were adapted from the public Report294 companion, source SHA-256

```
2673e4e5af78a3910e00057f1351588950b0471cb88a5d931e4add890986440a
```

This implementation adds exact formal substitution and coefficient extraction,
changes the documented budgets, and independently constructs the Report295
identities. No earlier companion or research module is imported or executed.
Reports 1–294 and their files are unchanged.

The mathematical input was the independently audited fixed-mean quartic proof
(source SHA-256 ecec37549c5ede6746a4726a3cc297a3fa18e78e7a34dd7867c64e2a07fa3b07)
and final all-order reflection proof
(source SHA-256 c26c095a6c037a695acfbf169ba81d7bcd3d0c766ceb7738e7536c83a5717264).
The independent reflection audit's Fraction/isqrt construction informed the
interval method; its code and data are not runtime dependencies. The separate
point-spike derivation informed the finite examples and energy formulas.
All data required to reproduce this companion is included in these five files.
