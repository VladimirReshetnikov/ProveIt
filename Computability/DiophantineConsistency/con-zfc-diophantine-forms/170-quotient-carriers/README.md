# Quotient carriers and integral projection for Diophantine consistency

Prepared for Vladimir Reshetnikov and the ProveIt repository, 25 October 2026,
with AI assistance.

This package supplies explicit ordinary polynomials with fixed integer
coefficients, together with ordinary proofs formalizable in ZFC that

\[
\mathrm{ZFC}\vdash\bigl(\text{the specified equation has no solution in its
declared domain}\bigr)\leftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

The proof constructs a finite syntactic ZFC refutation from a zero and
constructs a zero from a refutation. It does not decide consistency.

Read **`report/report.pdf`** for the complete article. Its LaTeX sources,
including a flattened `report_standalone.tex`, are included. The article
prints all 154 residuals of the principal quartic and the entire finite
recipe for the compact constants.

## Selected results

### Compact fixed equations

All variables in these four equations are **strictly positive integers**.

| Literal source in `compact/` | Variables | Binary operations | Exact degree |
|---|---:|---:|---:|
| `fixed_13_residue_70_degree206.json` | 13 | 70 | 206 |
| `fixed_13_residue_71_degree162.json` | 13 | 71 | 162 |
| `fixed_13_residue_q4_72_degree154.json` | 13 | 72 | 154 |
| `fixed_12_rational_74_degree438.json` | 12 | 74 | 438 |

An operation is one binary addition, subtraction, or multiplication,
including a square and multiplication by a small constant. Reuse and fixed
integer leaves are free. Every reported gate and input is live.

The complete coherent indexed943/radix67 tuple is supplied as four compressed
canonical byte strings, totaling **295,388 raw bytes**. The largest fixed
integer has **592,884 bits**. `compact/rebuild_fixed_coefficients.py`
reconstructs all four from the printed finite recipe and the literal
436-character seed. The operation counts do not include the bit lengths of
those constants. Coefficients after expanding the high-degree polynomial can
be larger than its fixed input integers.

The same tuple is used by the matched package-142 parents: 14 variables at
70 operations/degree 189, 14 at 71/157, and 13 at 72/433. The first two new
equations remove a variable without adding an operation. The third reduces
the matched 13-variable, 72-operation degree from **433 to 154**. The
12-variable equation uses two additional operations relative to the
13-variable anchored parent.

For an unrestricted-integer presentation of the last construction,
`equations/P36_integer.json` replaces each positive coordinate by
`1+a*a+b*b+c*(c+1)`. It has **36 integer variables, 158 operations, and
degree 876**. This standard domain conversion preserves zero existence;
the unmodified twelve-variable expression is not asserted to work over all
integers.

### Direct small-coefficient quartics

All variables here range independently over **unrestricted integers**.
Each equation is the sum of the squares of every supplied quadratic residual.

| Selected directory in `equations/` | Variables | Residuals | Degree | Expanded monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| `P217/` — principal | **217** | **154** | **4** | **19,112** | **5,184** |
| `P220_lowheight/` | 220 | 157 | 4 | 8,847 | **2,336** |
| `P220_sparse/` | 220 | 157 | 4 | **7,858** | 6,272 |

Height means the largest absolute coefficient of the fully collected quartic,
not the largest coefficient of a residual. Complete expansions are included
beside the residual lists. These direct constructions encode the numerical
proof calculus C222; they use neither K215 nor Jones's universal polynomial.

The pinned incoming Pooled Powers equation has 225 integer variables, 162
residuals, 7,867 expanded monomials, and height 128,446. The new sparse
220-variable equation improves all four of those figures. The 217-variable
equation gives fewer variables and residuals with a larger expanded support.
The incoming 234-variable quadratic-projection equation has 171 residuals,
19,050 terms, and height 4,480, which remains a distinct comparison point.

There is no global simplicity claim. The repository already contains a
37-integer-variable quartic with a large fixed coefficient architecture,
nine-positive-variable equations with much higher degrees and circuit costs,
and many other tradeoffs. Counts across domains and coefficient architectures
must remain separate.

## What is new

### A Pell ordinate carries an omitted quotient

The compact parent has a positive quotient `h` with
`k-h*E-R=1`. Instead of quantifying `h`, the first two new constructions use
the existing combined Pell root through the polynomial carrier

```
t = E*n-k+R.
```

The free strong Pell multiplier is scaled so that an auxiliary ordinate is
`+1` or `-1` modulo `E`. The first Pell root is `1` modulo `E`. Signed main
index recovery authenticates the rank before the missing quotient is used.
A bound then turns a congruence into `2*r=R+1`; a growth comparison excludes
the other sign. This restores the positive integer
`h=(k-R-1)/E`.

Removing the quotient factor saves four arithmetic gates; scaling the
multiplier and computing the carrier costs four. Thus the variable disappears
at the same operation count. Completeness chooses a fresh suitable strong
Pell pair and then recomputes its auxiliary witnesses.

The smaller-modulus refinement uses

```
t = q^4*n-k+R,
```

and scales the multiplier only by the already computed `q^2`. Divisibility
of the auxiliary squared base by `q^4` suffices. After recovering the exact
first index modulo `q^4`, the full first-Pell recurrence restores divisibility
by `E`. This gives the 72-operation, degree-154 result.

### An integral rational carrier removes another quotient

The twelve-variable construction applies the retained adjacent-Pell
integrality theorem to the proof-only substitution

```
t = n+(k-R-1)/E.
```

Clearing the denominator gives an ordinary polynomial. Coprime valuation
arguments recover its square roots; the adjacent Pell equation then forces
`t` to be integral. Thus `E` divides `k-R-1`, and the parent quotient is
restored. The rational-integrality theorem is inherited, not claimed as a
new theorem here. Its application to this inexpensive anchored parent is
the new reduction.

### A direct composition with explicit inverse maps

The principal source uses the affine radix class `q=6*z+3`. Both `q` and
`q+1` are nonzero nonunits before signs are known, allowing the pooled
power certificates to recover the needed nonnegative indices immediately
after Pell orientation. The ordinary proof treats a negative radix and
the boundary beta spacing separately.

The principal chain is:

```
242 variables / 178 quadratic rows: new arithmetic source
238 / 174: exact affine projections
234 / 171: inherited strict-horizon method
223 / 160: inherited fixed-base power pooling
217 / 154: six inherited common-quadratic-direction projections
217 / 154: 112 reversible integer row operations.
```

The 220-variable companions begin with the unchanged incoming Pooled Powers
equation and use only exact integer zero-set bijections and reversible row
operations. They do not require the new semantic bootstrap.

The choice `F=t^t`, its use as binomial shift, and the linear odd beta spacing
already occur in the incoming **Linear CRT** archive. Strict local horizons,
pooled powers, and common-quadratic-direction projections are also prior
work. This package supplies new carriers, a distinct affine-radix bootstrap,
and tested compositions with literal output equations. It does not claim
literature-wide priority.

## Verification

From the archive root, with Python 3.10 or newer:

```sh
python3 -B verify_release.py
python3 -B -O verify_release.py
```

The mathematical checks require only the standard library. They are read-only
with respect to the sealed package; temporary extraction and deterministic
upstream rebuilds use temporary directories. To write a fresh receipt:

```sh
python3 -B verify_release.py --receipt /tmp/conzfc-release-check.json
```

The checks cover exact arithmetic programs and all live gates, full symbolic
homogeneous leaders, coefficient reconstruction, parent source bindings,
strict-range and pooled-power identities, all frame atoms, integer restoration
maps, inverse row operations, every quartic coefficient, the printed principal
residuals, and deliberate corruption controls. Normal and optimized Python
runs and fresh runs from other working directories are included in the
component receipts.

`evaluate.py --help` explains evaluation of a residual list or an arithmetic
program at a supplied integer tuple. Use its optional modulus for convenient
checks with the large compact constants. A modular zero is not an integer
zero and is not evidence of a refutation.

Finite checking does not replace the unbounded ordinary proofs. The new
theorems have not been rebuilt end to end in Lean or Rocq, and no encoded
object-language ZFC proof string is claimed. Separate reviews in this work
are independent AI-assisted mathematical reviews, not outside human refereeing.

## Files

- `report/`: article, PDF, all TeX fragments, flattened TeX, and principal
  residuals generated directly from the canonical data.
- `equations/`: convenient exact copies of the three selected direct equations
  and their complete expansions, plus the 36-integer compact lift.
- `compact/`: four new compact equations, full proof, finite constants, producer,
  independent checker, reconstruction script, immediate parents, source closure,
  and original notices.
- `direct/`: arithmetic source and complete transformation chain, all certificate
  stages required by its verifier, selected and alternative profiles, original
  upstream archives, unbounded proofs, and finite checks.
- `review/`: separate mathematical and literal-source reviews.
- `additional/ordinate_normalization/`: a separate 17-witness universal-compiler
  result at 91 operations/degree 269; it is not a new smallest fixed consistency
  equation.
- `code/`: principal residual renderer and integer-domain lift tools.
- `SOURCES.json`, `SOURCE_AUDIT.md`: immutable comparison snapshot and read scope.
- `MANIFEST.sha256`: integrity hashes for the packaged files.

The comparison commit is
`536c08e7913e59bd42e8fca66e89944c920884ad` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
All twelve incoming ZIPs at that commit were fetched and checked against their
Git blob hashes and byte lengths; the audit distinguishes reading a package's
comparison material from replaying its complete verification.

## Rebuilding the PDF and integrating the submission

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The standalone TeX file contains the same article with its local inputs
expanded. PDF bytes may vary with the TeX distribution; canonical JSON data
define the equations. The full report was compiled and visually inspected.

This is an additive submission suitable for `docs/incoming`, followed by
placement in the existing collection. No existing repository file was modified
or remotely published. Retained parent copies can be deduplicated at intake by
their exact hashes and pinned locations. New material follows the root MIT
No Attribution license; inherited third-party notices remain in their original
source directories and archives.
