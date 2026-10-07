# Exact companion to Report293

This public companion uses only the Python standard library. It reconstructs the
finite geometry, ordered additive quadruples, integer relation lattices, and
formal polynomial identities used in Report293. No package installation,
network connection, computer algebra system, numerical optimizer, or private
research file is needed. Python 3.10 or later is required; the release was tested
with Python 3.12.

From the report directory:

```
python -I -B -X int_max_str_digits=640 companion/exact_checks.py
python -I -B -X int_max_str_digits=640 tests/test_companion.py
python -I -O -B -X int_max_str_digits=640 companion/exact_checks.py
python -I -O -B -X int_max_str_digits=640 tests/test_companion.py
```

The checker accepts no arguments, reads only its bundled
`companion/lattice_certificate.json`, and writes deterministic exact JSON to
standard output. It creates no files. Redirect standard output if a saved
receipt is wanted. Its normal and optimized outputs are byte-for-byte identical.
There are no timestamps, absolute paths, floating-point approximations, platform
versions, or unordered-set output in the receipt. Every mathematical guard uses
an explicit exception, so optimization cannot disable validation. The tests
also check that the checker contains no Python `assert` statement.

The certificate is compact, canonical JSON: sorted keys, no optional whitespace,
and a final newline. Its SHA-256 is
`443f440b6a31da4c0e784675d443460773a7b3be06f008d42dee397d66d2dd3d`.
The checker regenerates its entire content, compares it with the bundled file,
and separately validates the supplied transformations.

## What the finite certificates prove

### Complete integer-lattice calculation

For the nonaligned exceptional-edge normal form, the nine formal values in the
variable order `(v,b,c)` are

```
(0, v, 2v)
(b, b+v, b+2v)
(c+v, c+2v, c)
```

The program constructs all nine transversal lines directly from the affine
plane, translates each triple by its first value, and obtains exactly six
distinct triples. For each triple it forms the three integer relations obtained
by choosing a midpoint. Every one of the `3^6 = 729` choices is checked.

For a choice, let `M` have six rows, each containing the three integer
coefficients of the chosen relation. The certificate includes:

- The six midpoint choices and all entries of `M`
- An explicit integer `6 x 6` matrix `U`
- The complete reduced matrix `R`, including its zero rows
- An index into the eight displayed column-lattice bases

The validator checks `det(U) = +1` or `-1` and `U M = R` by exact arithmetic.
Eight further unimodular transformations connect the displayed column bases,
after transposition, to the same nonzero row bases. Thus the certificate checks
737 explicit unimodular identities. Both containments of each integer lattice
follow from these identities; the calculation does not replace integer span by
rational span, saturate a lattice, or divide by an integer in the target group.

The eight displayed column bases have counts
`690, 1, 1, 1, 3, 27, 3, 3`. Exactly 693 choices force `3v=0` and are excluded
in this branch. Each of the remaining 36 forces `6v=6b=6c=0` and
`3b,3c in {0,3v}`. Membership is checked in the actual integer row lattice.

This finite enumeration is universal for arbitrary abelian targets: a map
realizing a midpoint choice annihilates its integer relation lattice, and
additional target relations only pass to a quotient. It is not sampling of
finite target groups. The report proves why the normal form and six conditions
cover the relevant structural case.

Other finite algebraic checks include all nine high-direction midpoint choices,
all 27 exceptional-edge placements with explicit affine normalizations, and all
30 partitions of nine. The `(8,1)`, `(7,1,1)`, and `(7,2)` derivative assignments
are tested using formal cycle-relation lattices; the first two are excluded and
exactly nine `(7,2)` placements remain. All possible `(6,3)` cycle-count lists
are also checked, including the collapse forced by the mixed list `(0,1,2)`.

### Formal polynomial identities, not parameter sampling

The small `Polynomial` class represents every polynomial as a dictionary from
monomials to exact rational coefficients. Equality compares every coefficient.
There are seven independent real centered variables, with the eighth nonorigin
value set to minus their sum. Therefore checking the centered identities proves
them for every real `h` with `h(0)=sum(h)=0`, including signed `h`.

Nineteen coefficient identities verify:

- `b*b = 7*1 + delta_0` and `b*h = -h`, and the constants
  `S(b)=8`, `P(b)=8`, `A(b)=48`, `C(b)=56`, `B(b)=456`
- The centered expansions of `A`, `B`, and `C`
- The retained and total energy expansions, independently reconstructed from
  all 729 ordered additive quadruples
- The full centered expression for `N-kappa*L`
- The Fourier identities for `S,P,A,B,C`, with imaginary coefficients represented
  exactly as `sqrt(3)` times rational polynomials
- The Fourier-inequality residual `(R-X)(8R-5X)`
- The completed-square bracket
- The scalar double-root factorization modulo `3u^4+48u^2-456=0`
- The unit-mass Cauchy residual `(8t-m)^2` and orthogonal mean coefficient `9/8`

The exact factorization is

```
t^4 + 48t^2 m^2 + 456m^4 - 224 kappa_* t m^3
  = (t-u m)^2 (t^2 + 2u t m + (3u^2+48)m^2),

u^2 = 6 sqrt(6)-8,
kappa_* = (11+6 sqrt(6))/(7u) = u(u^2+24)/56.
```

The checker first verifies the factorization with a formal `u`, leaving exactly
a multiple of the stationary polynomial. Separate arithmetic in
`Q[s]/(s^2-6)` verifies the stationary relation and equivalent expressions for
`kappa_*`. It checks `F(2)=83/56<3/2`, so the required averaging parameter lies
in the proved interval. It verifies the exact comparison `7/12 < lambda` via
`27633-11106 sqrt(6)>0`, using `sqrt(6)<49/20` and the positive rational residual
`4233/10` after substitution. Positivity of `u^2` is checked from `sqrt(6)>2`.

For the fixed-spike unit-mass stability corollary, it additionally verifies
`kappa_*^2=1+81 sqrt(6)/196` and `c=1-4 kappa_*^2/9=5/9-9 sqrt(6)/49`.
The bounds `2<sqrt(6)<5/2` give the exact rational bounds
`0<85/882<c<83/441<1/2`. The coefficient identities also check the Cauchy and
orthogonal-decomposition algebra in that corollary. The analytic stability
estimate and its fixed-plane, fixed-map scope are supplied by the report.

These identities certify the algebra used in the proof. The report supplies the
Cauchy inequalities, signs, strictness argument, and boundary reasoning that
turn the identities into the unrestricted spike lower bound and its unique
positive scaling ray of minimizers. No finite grid is offered as a substitute
for those analytic arguments.

## Explicit witness counts

Points are ordered row by row: `(i,j)` with `j=0,1,2` outermost and `i=0,1,2`
innermost. All energies use ordered quadruples. Each fixed witness is counted
both by direct source-triple enumeration and an independent ordered-pair
convolution implementation.

- Order-nine pattern `000 / 222 / 147`: `(E_a,E)=(369,729)`
- Aligned cap `010 / 101 / 010`: `(425,729)`
- Two-point pattern, with weight two on its containing line: `(1330,2322)`
- Either cross-branch pattern, with weight two on the last row: `(1354,2322)`
- Nonaligned low binary pattern: `(417,729)`
- Generic high branch `3c not in {0,delta}`: retained row-sum-residue slices
  `(87,87,187)`, hence `(361,729)`

The generic count uses the formal conditions “equal integer row sums” and
“even difference of spike multiplicities”; it does not choose a finite target
model. The report proves equivalence with target respectedness in this branch.
The receipt records every branch bound and verifies their maximum is
`677/1161`, with `677/1161 - 425/729 = 4/31347 > 0`. This is the uniform witness
bound outside the affine, cut, and affine-plus-single-spike plane families;
the program does not claim that `677/1161` is an optimal second extremum.

For the pure order-two spike with exceptional weight `t` and eight unit weights,
coefficient counting gives

```
N(t) = t^4 + 48t^2 + 456,
E(t) = N(t) + 224t,
N(t)-tN'(t) = 456-48t^2-3t^4.
```

## Supplementary sanity checks and limits

The 512 binary maps split into seven affine/complement orbits of sizes
`2,24,18,72,144,144,108`. The program checks their disjointness and completeness,
the derivative-energy identity, and the constant-derivative family test.
It also tests the centered Fourier inequality on all `3^7=2187` signed integer
parameter choices, recording minimum nonzero slack 24.

These binary-map and signed-grid tests are diagnostics only. They neither
classify maps to arbitrary targets nor prove an inequality for all real weights.
The universal parts are the complete relation-lattice certificates and the
formal coefficient identities, used with the report's structural and analytic
proofs. In particular, infinite-dimensional affine-plane gluing is a theorem in
the report, not an inference from testing a few ranks. No numerical optimization
or exploratory numerical data is imported or used.

## Input validation and tests

The public exact energy helper supports nine exact integer or rational weights,
with numerators and denominators at most 256 bits, and nine integer target
values, either in `Z` or modulo a positive integer. Integer matrix inputs have
at most 16 rows and columns and 4096-bit entries. The intentionally bounded
interfaces reject booleans, floating-point numbers, ragged matrices, negative
weights, all-zero weights, bad dimensions, and unknown methods.

The certificate loader bounds file size at two megabytes and rejects duplicate
JSON keys and nonfinite JSON constants. Certificate replay rejects omitted or
duplicate choices, unknown fields, wrong generators, incorrect ranks or basis
indices, invalid transformations, and nonunimodular matrices.

The 37 tests cover these adversarial cases, exact fractional weights, zero-weight
boundaries, affine-addition invariance, polynomial identities and deliberate
nonidentities, integer-lattice versus rational-span membership, certificate
replay, optimized execution, byte-identical output, arbitrary working
directories, unknown CLI arguments, and read-only execution. Both interpreter
modes run the same guards and pass the same suite.
