# Shared factorial errors: explicit Diophantine equations for Con(ZFC)

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026.

Start with **report/report.pdf**. Its self-contained editable source is
**report/report.tex**. The main equation and both companions are literal
polynomials with fixed integer coefficients and unrestricted integer unknowns.

## Completed results

Each equation is the sum of the squares of its complete quadratic residual
list. Each has an integer zero if and only if a finite ZFC refutation exists,
by the ordinary mathematical proof in the report composed with the identified
inherited C222/refutation calibration. Hence ZFC proves its integer
unsolvability equivalent to Con(ZFC).

| Profile | Integer variables | Quadratic rows | Degree | Collected terms | Height |
| --- | ---: | ---: | ---: | ---: | ---: |
| Main, fewer variables: `equations/equation240` | 240 | 177 | 4 | 21,482 | 6,144 |
| Balanced: `equations/equation241_affine_balanced` | 241 | 178 | 4 | 5,351 | 15,107 |
| Lower coefficients: `equations/equation241_affine` | 241 | 178 | 4 | 9,544 | 4,512 |
| New arithmetic core: `equations/candidate244` | 244 | 181 | 4 | 5,346 | 128,446 |
| Matched incoming parent: `equations/parent252/equation` | 252 | 182 | 4 | 5,340 | 128,446 |

The balanced 241-variable equation stays close to the parent's monomial count
and reduces its coefficient height substantially. The 240-variable equation
uses more monomials to remove one further coordinate. The main report prints
all 177 residuals of the 240-variable equation. Every companion's residuals
and complete expansion are supplied as JSON.

These are improvements in the direct C222 branch. The repository also has
few-variable constructions with different coefficient architectures, including
a 37-integer quartic. No global simplicity minimum is claimed.

## The new mathematical step

Let `M` be the existing common denominator for eleven normalized modular
remainders `R_i`. Introduce a normalized factorial error `S` and a ratio `v`:

    B*v = M
    M*F = v*V + S
    M^2 = 1 + 4*(S^2 + sum(R_i^2)) + a^2 + b^2 + c*(c+1)

The norm immediately implies `M != 0` and
`|B*F - V| < |B|/2`, without assuming signs. A nearest-integer factorial
lemma later forces `F=t!`. This permits removal of the two former private
factorial positivity certificates.

The centered remainder argument also permits the initially signed affine
odd radix `q=2*z+1`. Unit-radix cases are ruled out through the common
denominator, and negative-radix binomial digits recover `B>0`, `F>0`, and
then `q>0`. The original beta formula `y=V*(V-1)` is retained.

The full fourteen-pair orientation pool is used by this proof and is preserved.
The final affine eliminations and integer row operations are separately
certified finite algebra, with explicit inverses.

## What is fully specified

- `equation.json`: every variable and every residual.
- `expanded_polynomial.json`: every collected coefficient of the quartic.
- `METRICS.json`: exact finite measurements.
- `transformation.json` and `RESTORATION.json`: reversible row operations,
  affine eliminations, and the complete map back to the arithmetic core.
- `equations/candidate244/`: raw changed source, complete monic projection,
  coordinate translations, and the final core equation.
- `equations/parent252/`: the complete retained direct parent, its exact
  source pins, ordinary proof closure, and immediate logical interfaces.

A sparse term `[c,[i,j,...]]` denotes `c*x_i*x_j*...`, with zero-based
coordinate indices. Repeated indices denote repeated factors. The empty
index list denotes a constant. There are no variable exponents, factorials,
floors, binomial primitives, universal-polynomial placeholders, or hidden
coefficient choices in the final polynomial data.

## Verify and rebuild

Python 3.10 or later with its standard library is sufficient. From this directory:

    python3 -B verify_release.py
    python3 -B -O verify_release.py
    python3 -B verify_release.py --rebuild

The rebuild mode uses a temporary copy and compares all selected mathematical
JSON files byte for byte. Normal verification preserves the supplied equations.
Use `--receipt /outside/path/receipt.json` to keep a new receipt without
changing this sealed package.

To regenerate the self-contained report and compile its PDF:

    python3 -B build_report.py

To regenerate only TeX, add `--tex-only`. A standard pdfLaTeX installation
with the packages listed in the preamble is sufficient. PDF metadata may
differ after recompilation; the polynomial coefficients do not.

## Proof and review scope

The report supplies ordinary unbounded proofs and identifies all inherited
interfaces. Exact finite checkers validate the new source mutation, restoration
maps, every original-row pullback, complete coefficient expansions, and
intentional corruption controls. The printed TeX polynomials are parsed
independently and compared with their JSON coefficients.

No consistency or inconsistency result is asserted. No new end-to-end Lean,
Rocq, or encoded object-language ZFC proof is claimed. The included mathematical
reviews are independent AI-assisted reviews within this work, not external
human peer review. The full transitive proof-assistant dependency closure
was not rebuilt.

The simpler intermediate `equation249` and `equation250` lineage, and earlier
experimental variants, are retained only to make the construction and
comparison reproducible. The released primary endpoints are the three
profiles at the top of this README; the report proves the final signed
affine-radix construction.

## Provenance and integration

The inspected repository commit is
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`. `PROVENANCE.json` records the eight
incoming archives and their hashes. Existing source notices are preserved.
The C222, CRT, Pell, common-remainder, deterministic-center, projection, and
residual-basis predecessors are credited in the report.

Copy this as a new contribution directory rather than overwriting an existing
numbered package. `MANIFEST.sha256` seals the delivered files for local
integrity checking; it is not an external signature or a proof certificate.
