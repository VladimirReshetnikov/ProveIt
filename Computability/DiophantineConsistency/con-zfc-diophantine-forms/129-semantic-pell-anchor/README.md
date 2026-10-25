# Semantic anchors for Diophantine consistency

Prepared for Vladimir Reshetnikov, 24 October 2026.

This package supplies two **fully materialized ordinary quartic polynomials**
over **N = {0,1,2,...}**, an ordinary mathematical proof of their consistency
equivalence, exact reconstruction code, and independent finite verification.

## Main result

Let `r[0], ..., r[182]` be all the quadratic residuals in
`equations/natural234/equation.json`. The recommended equation is

    P234(x0,...,x233) = sum(r[j](x)^2 for j=0,...,182) = 0.

The complete list is also printed in the PDF appendix and supplied as
`equations/natural234/equation.txt`. Every collected coefficient is in
`equations/natural234/expanded_polynomial.json`.

The ordinary theorem, formalizable in ZFC, is

    ZFC proves:
    [there is no x in N^234 with P234(x)=0] iff Con(ZFC).

The analogous theorem holds for the 233-variable companion. Neither result
asserts Con(ZFC), its negation, or a numerical solution. No variable-exponent,
factorial, binomial, bounded-quantifier, or unspecified universal-polynomial
primitive remains in either final equation.

## Exact sizes

| Natural-number quartic | Variables | Quadratic rows | Degree | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Incoming shared-binomial parent | 319 | 254 | 4 | 10,283 | 86,842,335 |
| Incoming shared Pell bound | 261 | 194 | 4 | 31,679 | 85,566,955 |
| Its sparse companion | 292 | 225 | 4 | 6,140 | 83,933,334 |
| **Recommended here** | **234** | **183** | **4** | **9,019** | **87,741,134** |
| Smaller-variable companion | **233** | **182** | **4** | **50,762** | **88,674,690** |

The recommended polynomial saves 27 variables and 11 rows relative to the
261-variable construction and cuts collected support by about 71.5%. Its
coefficient height is about 2.5% larger. The 233-variable endpoint saves one
more coordinate but has approximately 5.6 times as many monomials.

These are improvements of the direct C222 arithmetic construction. They are
not global variable-count records or global simplicity optima. The repository
contains separate smaller-variable constructions with other representations
and tradeoffs, including specialized universal-polynomial quartics.

## The additional mathematical idea

The construction combines the inherited single Pell cap with the inherited
six-exact-power modular-binomial compiler. The enlarged frame includes all
modular upper indices, and a separate lower Pell witness leaves the principal
base free to satisfy the common-root congruence.

The new structural step **reuses the derived label polynomial J as the sole
fully indexed Pell pair**. In completeness, shifting one encoded CRT column
by the whole period N^2 preserves all local congruences and makes J larger
than every other requested index. The representative budget changes from
9*N^2 to 10*N^2. The pooled squared-error congruence then certifies the other
fourteen indices. No added inequality forcing J to dominate the requested
indices is needed in the polynomial: soundness derives their equality to the
bounded actual Pell indices, and completeness makes the required witness
choice.

The implementation also uses consecutive principal ordinates and the inherited
dominant modulus N*q^(x+1). Existing output rows enforce the correct orientation
of every consecutive pair. All steps and their noncircular dependency order are
proved in `report.tex` and independently reviewed in `proofs/`.

The numerical C222 calculus is calibrated to ZF and ZFC refutations by the
retained interfaces `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The constructor neither
reads nor simulates K215 and does not instantiate Jones's universal polynomial.

## Read and reproduce

- `report.pdf`, `report.tex`: complete report and all 183 principal residuals.
- `residuals234.tex`, `residuals233.tex`: complete generated LaTeX transcriptions.
- `equations/natural234/`, `equations/natural233/`: literal equations, expansions,
  certified substitutions, and measured summaries.
- `equations/source/`: common semantic graph and 344-variable normalized source.
- `equations/integer/`: explicit degree-eight recipes in 702 and 699 unrestricted
  integer variables, using `g(a,b,c)=a^2+b^2+c(c+1)`.
- `code/`: portable constructor, exact evaluator, independent checkers, and
  transcription generator.
- `upstream/`: frozen dependency closure and original notices.
- `provenance/`: exact comparison snapshot, original archive hashes, copied-file
  identities, baseline polynomial metrics, and logical interface statements.
- `verification/`: actual verification receipts.
- `SHA256SUMS`: all delivery-file hashes except the checksum list itself.

Use Python 3.10 or later; the standard library is sufficient. From this folder:

```sh
python3 -B code/verify_release.py
python3 -B -O code/verify_release.py
python3 -B code/verify_release.py --rebuild
```

`--rebuild` reconstructs both selected endpoints in a temporary directory and
checks all ten generated files for each endpoint byte for byte. It needs no
network or external repository checkout. All other checks are read-only by
default. `--output PATH` can record a receipt; use a path outside this package
after sealing it, so its checksum manifest stays unchanged.

To evaluate a supplied JSON array of coordinates:

```sh
python3 -B code/evaluate.py coordinates.json --variant natural234
python3 -B code/evaluate.py coordinates.json --variant natural233
python3 -B code/evaluate.py coordinates.json --variant integer702
python3 -B code/evaluate.py coordinates.json --variant integer699
```

This is exact evaluation at a point, not a method for deciding solvability.

To check or regenerate the complete printed equations:

```sh
python3 -B code/render_equations.py --check
python3 -B code/render_equations.py
```

To compile the report, use TeX Live with lmodern, amsmath, amssymb, amsthm,
mathtools, geometry, booktabs, longtable, array, microtype, xcolor, enumitem,
fancyhdr, xurl, hyperref, and listings:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Recompiling a PDF can change its byte hash; preserve the original release if
you want to check the shipped checksum manifest after rebuilding the document.

## Verification scope

The semantic audit checks 92 exact local bindings and the inherited source
prefix, with five deliberate corruptions rejected. The separate affine-export
checker imports no producer and checks every defining gate, restoration,
dependency closure, and raw coefficient. The contraction checker independently
replays 110 or 111 natural-domain restorations, including two rational
sum-of-squares nonnegativity certificates, and every final coefficient. A
changed final residual is rejected even after its target hash is updated.
Both normal Python and optimization-mode runs preserve the checks.

The full consistency equivalence is established by the written unbounded
arguments composed with the inherited calibration. Finite arithmetic controls
do not prove those unbounded theorems by sampling. The immediate retained Lean
interfaces match the pinned repository; this is not a fresh rebuild of their
entire transitive dependency graph or a newly emitted end-to-end Lean/Rocq or
object-language ZFC proof.

## Provenance and incorporation

All comparisons use ProveIt commit
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`.
The relevant incoming archive names and exact SHA256 hashes are in
`provenance/SOURCE_PINS.json`. Earlier arithmetic ideas are credited in the
report; novelty is claimed only relative to the inspected material.

This folder can be incorporated as a self-contained `semantic-pell-anchor`
research package. No repository files were committed, pushed, or published
as part of preparing this delivery.

New material uses the repository's MIT No Attribution license in `LICENSE`.
Inherited files retain their original notices. The mathematics, code, and
exposition were developed with AI assistance; no human review or institutional
endorsement is implied.
