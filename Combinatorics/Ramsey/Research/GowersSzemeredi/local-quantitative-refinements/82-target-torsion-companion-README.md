# Exact companion to Report294

This is a standalone, read-only Python standard-library companion. It requires
Python 3.10 or newer; the release was checked with Python 3.12. No installation,
network access, numerical optimizer, computer algebra system, or earlier report
files are needed. The mathematical proofs, including the structural reductions,
analytic inequalities, and arbitrary-rank arguments, are in Report294.

From the report directory, run:

```
python -I -B companion/exact_checks.py
python -I -B tests/test_companion.py
python -I -O -B companion/exact_checks.py
python -I -O -B tests/test_companion.py
```

The checker takes no positional or configuration arguments. It reads only the
bundled `companion/midpoint_certificate.json` and prints one canonical JSON
receipt to standard output. It does not create or modify files. Redirect stdout
if a saved receipt is wanted. Normal and optimized runs give byte-identical
receipts. They contain no clock time, absolute paths, platform data, floating
point approximations, or nondeterministically ordered sets. Every mathematical
guard raises an explicit exception and remains active under `python -O`.

Public inventory:

- `companion/__init__.py`
- `companion/exact_checks.py`
- `companion/midpoint_certificate.json`
- `companion/README.md`
- `tests/test_companion.py`

## What is proved by the certificate

The universal midpoint lemma is a complete finite statement about integer
relations, not a sample of target groups. In the formal variable order `(v,b,c)`,
the exceptional-edge grid is

```
(0, v, 2v)
(b, b+v, b+2v)
(c+v, c+2v, c)
```

The checker constructs all nine transversal lines from the source geometry. It
forms their three midpoint relations, normalizing each relation by its sign,
and checks that they are exactly the alternatives from these six triples:

```
(0,b,c+v)       (0,b,c-2v)
(0,b+v,c)       (0,b-2v,c)
(0,b+2v,c+2v)   (0,b-v,c-v)
```

Relation groups are sorted lexicographically in the certificate, so their
indices need not equal the displayed triple order. The receipt records the
mapping from all nine actual transversal lines to the six relation groups.

For every one of the `3^6 = 729` midpoint choices, the JSON certificate contains
its six chosen integer relation columns `R_j` and six explicit integer
coefficients `c_j`. The checker independently reconstructs the columns and
verifies, coordinate by coordinate,

```
sum_j c_j R_j = (6,0,0).
```

Every coefficient has absolute value at most 6. Thus every possible midpoint
choice implies `6v=0` in every abelian target. Extra target relations only pass
to a further quotient and do not invalidate that conclusion. No HNF routine,
rational-span replacement, lattice saturation, or division in the target group
is involved. Report294 then uses injectivity of doubling to conclude `3v=0`.

The certificate is canonical JSON with sorted keys, compact separators, and a
final newline. Its SHA-256 is

```
cb053838d26497a2e52890e56f3b2c98202c7b1c04bcb6218059fac74db2570a
```

The validator checks schema and exact types, the regenerated geometry, all
columns and coefficients, exactly 729 distinct choices, and full choice
coverage. It does not need to trust how the coefficient vectors were found.
A different valid bounded integer-combination witness would establish the same
lemma, but would change the public file hash and receipt.

## Exhaustive cycle coverage and the plane counts

The checker generates all 30 partitions of nine and identifies all those with
square sum greater than 35. It then enumerates all distinct labeled placements
of the relevant derivative multiplicities into three oriented three-cycles:

- `(8,1)`: 9 placements
- `(7,2)`: 36 placements
- `(7,1,1)`: 72 placements
- `(6,3)`: 84 placements
- `(5,4)`: 126 placements
- `(6,2,1)`: 252 placements
- `(6,1,1,1)`: 504 placements

A cycle with three distinct increment labels fails the AP condition. For each
remaining impossible placement, a directly checked integer combination of the
three cycle-sum equations forces either equality of two labels or twice their
difference to vanish. The latter is a contradiction under injective doubling.
The coefficient search is bounded by 2 in absolute value, but its successes
are checked as exact identities; it is not a target-group search.

The only surviving `(6,3)` cycle profiles are two constant cycles and the other
constant cycle, or three `(v,v,u)` cycles. The only surviving `(6,2,1)` profile
is two all-majority cycles and one `(u,u,w)` cycle. No `(5,4)` or `(6,1,1,1)`
profile survives. The receipt includes the exact case counts. It also checks
all 27 exceptional-edge placements, with explicit affine source changes: 9
aligned and 18 nonaligned. All nine combinations of midpoint relations from
the two aligned transversal lines force `3v=0`, `6v=0`, or `3u=0`.

Source points are in lexicographic order. For a plane, the first coordinate is
the row and the second coordinate is the column. Energies count ordered
quadruples. The normalized pattern `000 / 222 / (-2,1,4)` gives:

- A formal infinite-cyclic representative: `Q=(41,33,33,33)` and energy 361
- An exact order-nine generator: `Q=(45,33,33,33)` and energy 369

Both energies are independently reconstructed from ordered triples and from
ordered-pair convolution, and satisfy `E_a=81+2 sum Q`. The generic histogram
calculation is universal under the report's hypotheses: the checker verifies
that every potential collision between distinct formal derivative values has
coefficient difference 3, 6, or 9. Injective doubling and `9q != 0` exclude
all three. The order-nine computation is faithful because `q` has exact order
nine. Thus these counts do not extrapolate from a few finite target examples.

The line calculation similarly groups all 27 ordered quadruples by their
formal target defects. There are 15 always-retained terms and four additional
terms for each true midpoint relation, giving `15+4m` exactly. Rational
arithmetic verifies `361/729 < 41/81 < 5/9`.

## Formal polynomial identities

The sparse `Polynomial` class represents a polynomial by every monomial and
its exact rational coefficient. Equality compares the entire coefficient
mapping. No parameter grids, interpolation, randomized identity tests, or
floating-point decisions are used.

For three nonnegative weights, put

```
N = x^4+y^4+z^4+4(x^2 y^2+x^2 z^2+y^2 z^2).
```

Direct symbolic enumeration on `C_3` verifies the target pattern `(0,0,t)` has
`E_a=N` and `E=N+4xyz(x+y+z)` when `0,t,2t` are distinct. The exact SOS is

```
N-5xyz(x+y+z)
 = ((x^2-y^2)^2+(y^2-z^2)^2+(z^2-x^2)^2)/2
   +5((xy-yz)^2+(yz-zx)^2+(zx-xy)^2)/2.
```

For arbitrary complex Fourier coefficients `A,B,C`, their conjugates are
represented by independent formal variables. Coefficient comparison checks

```
sum_cyclic |A^2+2BC|^2
 = N_complex + 4 Re(sum_cyclic A^2 conjugate(BC)).
```

This is the algebra used in the arbitrary-kernel three-fiber Fourier proof.
The report supplies the absolute-value inequality and the SOS application.
Identical fibers give the exact coefficients 15 and 27, proving the equality
calculation used for the fixed-rank `5/9` construction.

### The nine-coordinate reflection

The reflection proof algebra checks:

- The Pearson square expansion under centered unit-variance moment constraints
- All eight two-value multiplicity formulas for nine equally weighted atoms,
  with squared skewness `(9-2k)^2/[k(9-k)] = 81/[k(9-k)]-4`
- The sharp squared skewness bound `49/8`, with equality only at `k=1,8`
- The derivative numerator of `4rs/(r^4+6r^2+1+s^2)`
- The critical-point substitution `s^2=3y^2+6y-1` and the resulting
  `G(y)=(3y^2+6y-1)/[y(y+3)^2]`
- The cross-multiplied derivative identity equivalent to
  `G'(y)=-3(y-1)(y+1)^2/[y^2(y+3)^3]`
- The centered and reflected fourth-moment expansions in eight independent
  centered coordinates, with the ninth equal to minus their sum
- The reflection lower-bound rearrangement, mean reversal, and `H_9^2=I`
- The exact fourth-power expressions at the displayed extremizer
- The circle-average identity `average Re(e^(i theta)z)^4=(3/8)|z|^4`

The last identity is checked by extracting the constant Laurent coefficient;
there is no numerical integration. The real-to-complex argument itself is in
the report. Likewise, compactness, Lagrange multipliers, positivity, endpoint
monotonicity, and the zero-variance and zero-third-moment cases are proved
there. The code certifies their algebra, not those analytic principles by
finite testing.

Exact arithmetic in `Q[sqrt(6)]` checks, for

```
u^2=6sqrt(6)-8, v=11+6sqrt(6), k=7u/v,
lambda=1/(1+k), rho=(1-k)/(1+k),
```

the stationary relation `3u^4+48u^2-456=0`, the simplification
`u^4+48u^2+456=32v`, and the equality between `G(u^2/8)` and `k^2`.
The rational bounds `2<sqrt(6)<49/20` show positivity and `k^2<1/2`, hence
`0<rho<1` and `lambda>5/9`. In this text, `rho` is a fourth-power lower ratio,
not the lower ratio of norms. The sharp lower norm ratio is `rho^(1/4)`.

## Spike energy, Fourier blocks, and product examples

Independent ordered-triple and ordered-pair polynomial counts on `F_3^2`
verify, with weight `t` at the origin and 1 at the other eight points,

```
E_a = t^4+48t^2+456,
E   = t^4+48t^2+224t+456,
E_s = t^4+48t^2-224t+456.
```

They also verify the parity identity `2E_a=E+E_s`. Together with the preceding
radical identities, this gives the exact quotient value `lambda` at `t=u`.
The order-two condition is essential to the parity identity.

The quotient character orthogonality identity is checked in `Q[zeta]`, where
`zeta^2+zeta+1=0`. It gives the coefficient `2/9` in the nine-frequency block
reflection. The report proves that any surjective linear quotient onto
`F_3^2` gives these blocks in arbitrary rank. The quotient must be linear;
an arbitrary surjection of sets does not provide this argument.

Two explicitly labeled supplemental checks are included:

1. On `F_3^3`, all 729 point/frequency coefficients of
   `(sf)^hat(xi)=f^hat(xi)-(2/9) sum_eta f^hat(xi+eta)` are verified. This is a
   coefficientwise identity for every function in that finite example, not a
   test of one selected function. The frequency space has three blocks of nine
2. The nonconstant, non-full-support kernel weight `h=(1,2,0)` has `E(h)=33`.
   Exhausting the rank-three ordered quadruples gives each of the three spike
   polynomials multiplied by exactly 33. Thus the construction attains
   `lambda` at `t=u` with nonuniform kernel weights. A separate three-fiber
   example gives retained energy 495 and ordinary energy 891, ratio `5/9`

These supplemental examples do not prove arbitrary-rank tensor factorization
or the infinite-dimensional passage. Those are exact arguments in Report294:
the product weights split the energy factors, and every finite support can be
enlarged to a finite-dimensional subspace preserving quotient surjectivity.

The companion does not assert classification of all extremizers. For each
fixed vector space V of dimension at least two (finite or infinite) and each
fixed nontrivial abelian target H, the combined target-sensitive weighted
maximum over maps outside the affine and translated index-three affine-cut
families is `lambda` when H has nonzero 2-torsion and `5/9` otherwise. The
companion does not assert the sharp fixed-rank indicator constant in targets
with nonzero 2-torsion. In targets without nonzero 2-torsion, both the weighted
and indicator constants are `5/9`.

## Validation and bounded interfaces

The public energy helper accepts ranks 1 through 3, exactly `3^rank` integer
target values, and nonzero nonnegative integer or Fraction weights. A positive
integer modulus selects a cyclic target; `None` selects `Z`. The two methods
are `quadruples` and `pairs`. All rational numerators and denominators and all
integer inputs are bounded to 512 bits. The vector validator additionally bounds
length to 1 through 32 and requires an exact nonnegative coordinate bound.
Booleans, floats, negative or all-zero
weights, bad dimensions, and unknown methods are rejected.

Polynomial input is bounded to 12,000 terms, 32 variables, total degree 16,
20-character identifier names, and 512-bit exact coefficients. Multiplication
has a two-million-pair budget. Evaluation requires exactly the relevant
variables and bounded rational inputs. Coefficient mappings are immutable.

The strict certificate loader reads at most 300,001 bytes and rejects anything
over 300,000 bytes, duplicate keys, floating or nonfinite numbers, overlong
integers, malformed JSON, and nesting beyond depth 16. Schema validation additionally
rejects missing or unknown fields, invalid dimensions or exact types,
duplicate/missing choices, altered geometry, and false linear combinations.
Canonical encoding is checked before the receipt is emitted.

The 51 adversarial tests exercise these rejection paths and deliberate algebraic
nonidentities. They also check exact fractional and zero-boundary weights,
independent energy algorithms, `-O` execution, identical receipts, arbitrary
working directories, unknown CLI arguments, and read-only execution. The
production checker contains no Python `assert` statement.

## Provenance and independence

The sparse rational-polynomial representation and several validation patterns
were adapted from the public Report293 companion `companion/exact_checks.py`,
whose source SHA-256 was
`3f40e23851e1d34485e971b241ad67ab58c2b8023c86b153d60ed89459a7779b`.
This implementation adds immutable coefficients, explicit operation budgets,
and derivative support, and introduces the Report294 identities and checks.
No Report293 module is imported and no earlier file is changed.

The midpoint coefficient vectors were obtained in an independent integer-
relations audit. This package preserves them as explicit witnesses and checks
each witness without importing the audit's construction algorithm. The
standalone audit-data source hash before canonical repackaging was
`cd620291041876a354e5a1f4c4d3b70b48d04fd9bb512d7b04f1c04fc9bba1f3`.
All data needed for verification is included in the public certificate.
