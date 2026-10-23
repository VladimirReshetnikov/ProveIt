# Structural reductions for explicit Diophantine consistency equations

Prepared for Vladimir Reshetnikov and the ProveIt repository, 23 October 2026.

**Main contributions:** a degree-30 polynomial in **14 strictly positive
integer unknowns**, with **83 arithmetic operations**, and a **quartic in
41 unrestricted integer unknowns**. Both have ordinary mathematical proofs,
using the explicitly identified inherited compiler and calibration results,
of the equivalence in ZFC between their unsolvability and `Con(ZFC)`.

The main paper is [report/report.pdf](report/report.pdf), with editable source
[report/report.tex](report/report.tex). Each component also has a full proof
in Markdown, exact literal polynomial data, coefficient payloads, generators,
source pins, and reproducible finite checks.

## Results and comparisons

The repository snapshot is
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. The comparison includes the later
packages 54–59, rather than relying only on the older collection README.

| Equation | Domain | Unknowns | Exact degree | Binary operations | Comparison |
|---|---|---:|---:|---:|---|
| `positive14/polynomial.json` | Strictly positive integers | **14** | **30** | **83** | 14-positive degree 52 / 79 gates in 55/59; 15-positive degree 30 / 79 in 58 |
| `integer41/quartic41.json` | All integers | **41** | **4** | Not optimized | 45-variable quartic / 28 quadratic rows in 57; now 26 rows |
| `integer41/sextic36.json` | All integers | **36** | **6** | Not optimized | Named historical 42-variable sextic of 27/29 |
| `integer41/octic31.json` | All integers | **31** | **8** | Not optimized | Named historical 36-variable octic of 27/29 |
| `nine-positive-111/generated/split_111_positive.json` | Strictly positive integers | **9** | **1,781,068** | **470** | Degree 1,910,404 / 473 gates in 59 |

The fourteen-variable degree improves by 42.31%, at four additional gates.
The quartic saves four integer variables and two quadratic residuals.
The nine-variable degree improves by 6.77% with three fewer gates. The
sextic/octic comparison is to the explicitly named historical bounds, not an
exhaustive current frontier claim.

No result here is a global minimum. The 15-positive / 66-operation point
and the 15-positive / degree-24 point remain different tradeoffs. The
fewest-variable positive and integer records are not reduced.

## The new ideas

1. **An adaptive quotient modulus.** Make the Pell ordinate `Y` a direct
   coordinate. A monic square equation first recovers `q^3 | Y`. Use
   `U = Y^2`, whose degree is only two, to absorb the index quotient.
   Since `H = 4(X+1)Y+3`, one has `gcd(Y^2,H) | 9`, and therefore
   `U/gcd(U,H) >= q^6/9 > q^4 > R+2`. The resulting early index bound
   justifies the strong-rank lemma before the deleted quotient is restored.
   Only after rank recovery is full `U | k-R-1` obtained.

2. **Delayed sign recovery.** In the unrestricted quartic, replace separate
   square guards on the radix and quotient by `X = 2u^2`. The packing
   estimates work with `Q=|q|`; the Pell argument recovers `X=2^R` before
   the sign of `q` is known. The congruence `q=1 mod (2^d-1)` excludes
   the negative divisors `-2^t`.

3. **One product guard for two positive coordinates.** Substitute
   `w=4w_scale`, giving `|E|>3R+1`. Then a negative common sign of
   `eta,zeta` would force `n>R`, while the strong-rank/auxiliary equations
   force `p=R` and `p>n`. This contradiction permits one three-coordinate
   guard for `eta*zeta>0` in place of two separate positivity guards.

4. **A smaller certified finite code.** The ancillary nine-variable form
   uses maximum position 111 and convolution height 2010, with exact
   coefficient isolation and a recalibrated valuation threshold. This is
   a modest packing improvement, distinct from the structural changes above.

The first three ideas retain the native K215 arithmetic endpoint but do not
use a universal Jones polynomial. The nine-variable companion retains the
inherited Jones finalizer. No independently validated smaller alternative
machine/proof-system endpoint was obtained.

## Exact coefficients

Each family binds a **whole** four-port tuple. All payloads are gzip streams
of minimal unsigned little-endian integer bytes. If the decompressed bytes
are `b[0],...,b[m-1]`, the integer is `sum(b[j]*256^j)`.

| Component | Tuple | `beta` | Four raw payloads |
|---|---|---|---:|
| `positive14/` | Source 44 compact complement layout | `2^590069 - 1` | 295,388 bytes |
| `integer41/` | Source 34 mixed parity unrounded layout | `2^1064921 - 1` | 532,479 bytes |
| `nine-positive-111/` | Source 31 original mixed layout | `2^1064921 - 1` | 533,099 bytes |

The two million-bit tuples are different even though `beta` agrees. Never
mix their other ports. `K0` is the `K` port. `MF` is the already shifted
`MF_source` port; do not add `beta` a second time. Every numeral and its
finite generator is included. No coefficient uses a consistency oracle.

## Reproduce

Python 3.10+, standard library only. From the extracted directory:

```sh
python3 verify_all.py
python3 verify_all.py --optimized
```

The root driver runs builders/checkers in temporary copies, confirms
byte-identical regeneration of the literal polynomials, reconstructs all
three complete native tuples, and writes receipts under `certificates/`.
The optimized replay verifies that Python `-O` does not bypass checks.
No network access is required.

For paper compilation, use a normal TeX Live installation:

```sh
python3 build_report.py
```

Before regenerating receipts or PDF metadata, verify delivered file integrity:

```sh
sha256sum -c MANIFEST.sha256
```

The checks prove finite source identities, exact polynomial identities,
degree/count certificates, and byte-level bindings. Modular evaluations and
bounded diagnostic cases do not prove the unbounded consistency equivalence.

## Proof status and domain

The proved mathematical assertion is the existence equivalence with a
finite syntactic ZFC refutation, followed by negation. This does not assert
that ZFC is consistent or inconsistent. `Con(ZFC)` refers to the repository's
specified recursive proof predicate.

The paper supplies ordinary mathematical proofs formalizable in ZFC, using
named inherited native-compiler, Pell, K215, and (for nine variables)
finalizer results. Their relevant source texts and exact pins are included.
The new literal equations have **no newly supplied end-to-end Lean/Rocq
certificate or object-language ZFC derivation**. The active repository's
separately checked equation remains distinct. Internal AI-assisted review
is not external peer review.

Fourteen and nine variables mean **strictly positive**, not arbitrary
integers. The nine-variable component includes a nonnegative-coordinate
companion of the same degree with 477 operations. The 41/36/31-variable
equations range over **all integers** without implicit sign restrictions.

## Layout and integration

- `report/`: complete PDF and editable LaTeX.
- `positive14/`: adaptive modulus proof, exact 83-gate circuit, native data.
- `integer41/`: quartic, its 44-variable intermediate, two elimination
  companions, exact sparse expansions and proofs.
- `nine-positive-111/`: certified positions/targets, polynomial circuits,
  all fixed leaves, source and finalizer proofs.
- `review/`: pinned baseline statements and independent internal review.
- `certificates/`: deterministic finite verification receipts and replay logs.
- `NOTICE.md`, `licenses/`: attribution; component notices remain intact.

This self-contained directory is suitable for placement beside the existing
numbered contributions. It makes no changes to their files or the active
formalized equation. The collection's next available directory number can
be selected during intake.
