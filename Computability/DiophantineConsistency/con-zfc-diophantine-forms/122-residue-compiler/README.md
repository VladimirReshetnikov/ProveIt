# One modulus for all binomial digits

## Two explicit quartic equations for Con(ZFC)

Prepared for Vladimir Reshetnikov and the ProveIt project, 24 October 2026.
Comparison snapshot: ProveIt commit `45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`.

The principal equation is

\[
P_{332}(z_0,\ldots,z_{331})=\sum_{j=0}^{262} Q_j(z)^2=0,
\qquad z_i\in\mathbb N=\{0,1,2,\ldots\}.
\]

Every quadratic residual is printed in `equation-332.pdf` and supplied in
`equations/natural332/natural/equation.json`. The complete collected polynomial
is supplied beside it as `expanded_polynomial.json`. There are no unspecified
constants or arithmetic functions remaining in the equation.

The ordinary proof in this package, composed with the explicitly pinned
C222/refutation calibration, gives

\[
\mathrm{ZFC}\vdash
\bigl(\neg\exists z\in\mathbb N^{332}\ P_{332}(z)=0\bigr)
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

The second equation has 333 nonnegative variables and substantially fewer terms.
It satisfies the same consistency equivalence. Neither construction assumes
that ZFC is consistent. Neither encodes a K215 execution or uses a Jones
universal polynomial or a large native coefficient tuple.

| Construction | Nonnegative variables | Quadratic residuals | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Pinned incoming Round14 parent | 349 | 268 | 4 | 12,768 | 86,915,503 |
| **This package: natural332** | **332** | **263** | **4** | **11,823** | **85,243,454** |
| **This package: natural333** | **333** | **264** | **4** | **4,357** | **209,508,384** |

Coefficient height is the maximum absolute coefficient in the fully collected
sum of squares. Domain matters: these are not counts of unrestricted integer
variables. The repository has separate constructions with smaller variable
counts, including a 37-integer quartic with very large fixed coefficients.
This package advances a specific direct, small-coefficient quartic frontier;
it proves no global optimality or historical-priority result.

## What changes mathematically

1. **A single existing denominator is enough.** The raw endpoint and factorial
   ceiling rows already imply `x > t+1,y+1`, before interpreting the factorial.
   Thus `M=N*q^(x+1)` contains every modulus needed by the binomial digits.
2. **Keep only the numerator residues.** One cofinal congruence for the Pell
   parameter makes `X_n+(q+1-A)*Y_n` a positive representative of `(q+1)^n`
   modulo `M`. Twelve full numerator powers disappear. One adjacent denominator
   power is a product, reducing the exact-power requests from nineteen to six.
3. **Arrange parity in the source.** The sparse variant makes every requested
   index even by choosing compatible proof and CRT certificates. It deletes
   index-gap coordinates without squaring the power outputs. Its common modulus
   is `N*q^x`, and `q^(2t)` is the square of `q^t`.

The general cofinal-Pell residue method was already present in ProveIt package
108. The general even-index obstruction was already in an incoming package.
The new results are the dominant-denominator argument, these combinations and
source changes, and their fully materialized equations. The proofs carefully
establish positivity, noncircular bootstrap order, and completeness after
regenerating the private Pell frame.

## Start here

- `report.pdf` / `report.tex`: research report and proof outline.
- `equation-332.pdf` / `.tex`: all 263 defining residuals, with no omissions.
- `equation-333.pdf` / `.tex`: all 264 defining residuals of the sparse companion.
- `proofs/MODULAR_NUMERATORS_PROOF.md`: detailed ordinary proof of the 332 form.
- `proofs/PARITY_PROOF.md`: detailed ordinary proof of the 333 form.
- `proofs/MATHEMATICAL_REVIEW.md`: independent mathematical review and limitations.
- `equations/`: original arithmetic graphs, projections, restoration certificates,
  exact residuals, full expansions, and construction metadata.
- `variables-332.tsv`, `variables-333.tsv`: coordinate-to-semantic-name maps.
- `residuals-332.tsv`, `residuals-333.tsv`: row labels, term counts and degrees.
- `SOURCE_LEDGER.json`: pinned repository, all eight inspected incoming archive
  hashes, parent metrics, and calibration source identities.
- `MANIFEST.json`: byte lengths and SHA-256 hashes of all shipped files other
  than the manifest itself.

## Verification and reproduction

Python **3.10 or newer**, with its standard library, is enough. No network,
symbolic algebra package, proof assistant, or repository checkout is required.
From this directory run:

```bash
python3 verify_all.py
python3 verify_all.py --rebuild
```

The first command authenticates the manifest, reconstructs every discarded
coordinate, checks all nonnegative monic contractions, re-expands every final
coefficient, checks the new modular and parity interfaces, and runs explicit
corruption controls. The second also rebuilds both constructions from the
vendored source and compares the selected outputs byte for byte. Rebuilds use
a temporary directory and do not replace the delivered equations.

For the check under optimized Python, with Python `assert` statements disabled:

```bash
python3 -O verify_all.py
```

The new independent checkers use explicit exceptions for their obligations.
They import neither the equation producers nor the inherited contraction
checker. In addition to all literal coefficient identities, finite regression
tests cover 1,920 Pell residues, 4,246 exact digits, 4,674 divisibility digits,
and 108 root-congruence cases where the factor 2 is not invertible.

The already performed checks and reproduction results are in `verification/`.
Their scope is finite algebra and structure. They do **not** search for a ZFC
refutation, test the consistency of ZFC, or replace the ordinary unbounded proof.
The inherited source calibration is also a mathematical dependency; this
package is not a newly compiled Lean/Rocq or object-language ZFC proof object.

Individual producers can be run into a new directory:

```bash
python3 code/release_332.py --output rebuilt/natural332 --parent vendor/round14/architecture/derived16_cantor
python3 code/even_architecture.py --output rebuilt/natural333 --modular --horizon 12
```

Their default dependency path is `vendor/round14/`, relative to the package.
`CONZFC_ROUND14_ROOT` can override it. The initial builder emits its own
receipts; the independent checkers remain separate.

To regenerate the complete printable equations and verify the actual typeset
algebra by parsing it back into sparse polynomials:

```bash
python3 code/generate_equation_tex.py
```

With a standard LaTeX installation, rebuild all three PDFs using:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error equation-332.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error equation-333.tex
```

Regenerating PDFs can change timestamps or layout with a different TeX version;
the fixed JSON equations and their collected coefficients are the canonical
literal mathematical definitions. Rebuilding files in place may require a new
manifest if their bytes change. `--skip-manifest` is an explicit release-preparation
option and is not used by the normal verifier command.

## Representation and hashes

A JSON term `[c,[i,j,...]]` means `c*z_i*z_j*...`, with zero-based indices.
An empty index list is a constant. Every index and coefficient is literal.

SHA-256 of the principal collected polynomial:

```text
3116335841f0b6d649e3289de4ed37e16f293e6fd82b23d37db22eae62baa4e7
```

SHA-256 of the sparse collected polynomial:

```text
3561fb559ade2ae06ae575c941287552a5b79a06d1918208fb18dbd02c6f6854
```

The ordinary quantified statement and its dependency boundary are explained in
the report. For positive integers replace every coordinate by `y_i-1`. A fully
specified unrestricted-integer companion can be obtained by substituting
`a_i^2+b_i^2+c_i(c_i+1)` in every coordinate, giving 996 integer variables and
degree eight; that elementary domain conversion is not an integer-size record.

## Provenance and licensing

See `NOTICE.md` and `LICENSE`. The vendored arithmetic source and calibration
copies are retained with their original identities and notices. Their historical
filenames may mention K-family machines; the theorem used here is the
machine-independent C222/refutation equivalence. The new polynomial construction
uses no simulation or execution of those machines.
