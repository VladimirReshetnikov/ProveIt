# Signed power recovery and coefficient-two quartics for Con(ZFC)

Research package dated **24 October 2026**, prepared for Vladimir Reshetnikov with AI assistance. The comparison snapshot is ProveIt commit `84e16e43092614bae262ca59651cb9d77e31a255`.

## Main results

Every unknown in this table ranges over **all integers**. Every final equation has **exact degree four** and fixed, fully supplied integer coefficients. “Rows” counts quadratic residuals whose squares form the single final polynomial.

| Equation | Variables | Rows | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Main quotient radius | **577** | 363 | 7,326 | 2,445,790,974,704 |
| Quotient radius, smaller coefficients | **582** | 368 | 6,069 | 964,213 |
| Output-square radius, smaller support | 586 | 372 | 7,059 | 2,445,790,974,704 |
| Output-square radius, smaller coefficients/support | 591 | 377 | 5,835 | 964,213 |
| Private units, coefficient alphabet **{-2, 1, 2}** | **3,564** | 3,350 | 14,518 | **2** |

The matched direct predecessors have 604 variables/9,676 monomials and 609 variables/8,823 monomials, respectively, at the same degree and heights. The quotient construction removes nine sign guards and all 27 of their private witnesses. The unit construction supplies a complementary small-coefficient equation; it has constant coefficient one.

For each equation the ordinary proof, composed with the explicitly identified inherited C222 calibration, establishes that **ZFC proves its absence of integer zeros equivalent to Con(ZFC)**. This is not a proof of consistency or an assertion of unsolvability independent of that equivalence. No new complete Lean or encoded object-ZFC proof object is supplied. These results improve specific direct-proof-certificate tradeoffs, not the repository's fewest-variable record or a proved global minimum.

## Read first

- `report.pdf` is the complete research article. Its appendix prints all 363 quadratic residuals of the principal 577-variable polynomial.
- `report.tex` and `sections/` are the complete LaTeX source.
- `quotient_frame/PROOF.md` gives the strongest radius argument and its dependency order.
- `signed_frame/PROOF.md` gives the squared-output companion.
- `height_two/PROOF.md` gives the private-unit collision proof and exact zero-set bijection.
- `review/REVIEW.md` and `review/QUOTIENT_REVIEW.md` give the independent mathematical assessments.

## Exact equation data

The main equation is the sum of the squares of all rows in
`quotient_frame/support8/equation.json`.
Its complete expanded coefficient list is
`quotient_frame/support8/polynomial.json`.

The smaller-coefficient companion is under `quotient_frame/support16_affine2/`. The two squared-output companions are under the corresponding `signed_frame/` directories. Each profile includes `projection.json`, the exact sequence of monic integer substitutions and inverse recipes against its supplied parent. A byte-identical `terminal_elimination_certificate.json` alias preserves the inherited optimizer's metadata convention.

The coefficient-two polynomial is in `height_two/anchored/expanded_polynomial.json`, with its residual list in `equation.json`. `certificate.json` identifies every reused product, new product, private unit and source-row reconstruction. Its `source.json` is byte-identical to `signed_frame/parent.json`. The height-two result uses the output-square parent; compiling the quotient parent instead is slightly larger and is not the preferred point.

In every sparse list, `[c,[i,j,...]]` means `c*x_i*x_j*...`. An empty index list is the constant monomial. Coordinates and row indices are zero-based. The lists contain literal integers, not symbolic coefficient ports. There are no unstated positivity restrictions on the final equation's coordinates.

## Verification

Python 3 and its standard library suffice. From this directory:

```bash
python3 verify_all.py
```

For complete deterministic regeneration as well:

```bash
python3 verify_all.py --rebuild
```

To retain fresh receipts in a chosen directory:

```bash
python3 verify_all.py --output /path/to/receipts
```

The source reviewer imports no builder or optimizer. The independent projection verifier checks every monic definition, every surviving residual and every expanded coefficient. The unit checker independently verifies all source pullbacks, product/unit equations and all 14,518 collected coefficients. The full package was verified and rebuilt after relocation into its delivery layout. Focused normal/optimized checks and mutation controls are included; no large genuine ZFC refutation or enormous Pell witness was computed.

The top-level `MANIFEST.json` authenticates all delivered files except itself. Running the supported verifier does not modify normative data. Historical dependency programs are preserved for provenance; supported new entry points do not require running those historical emitters.

## Building the report

The appendix is deterministic:

```bash
python3 generate_rows.py
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

A standard TeX Live installation with common packages (`amsmath`, `amssymb`, `amsthm`, `mathtools`, `geometry`, `lmodern`, `microtype`, `booktabs`, `longtable`, `hyperref`, and `fancyhdr`) is sufficient.

## Provenance and proof boundary

`quotient_frame/provenance/` contains the intact 407/888 source archive and copies of fifteen later ordinary source/proof records, with a path/hash map. The original archive SHA-256 is:

```text
59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59
```

The inherited logical chain is numerical C222 derivability of code 1, finite ZF refutation, and finite ZFC refutation. The immediate named bridge statements and hashes were inspected. Their full transitive Lean closure was not rebuilt here. The arithmetic reductions use the direct proof-certificate source; they do not simulate K215 or instantiate Jones's universal polynomial.

Inherited material retains its original notices and license. `LICENSE.UPSTREAM` preserves the repository license. New material is AI-assisted research for incorporation into ProveIt. No upstream repository files were modified or pushed during this investigation.
