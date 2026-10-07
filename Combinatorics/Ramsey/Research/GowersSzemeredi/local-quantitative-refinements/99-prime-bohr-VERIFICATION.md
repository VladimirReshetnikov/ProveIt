# Verification record

## Mathematical scope

The article gives ordinary proofs of:

1. The CRT parameter construction and full component classification.
2. The exact mass formula and finite-grid discrepancy/run count.
3. The prime-cyclic lower obstruction with its quantifiers and explicit cutoffs.
4. Persistence on a nonzero interval of radii and individual essentiality of every constraint.
5. The probability-measure identity and approximation/translation tradeoff.
6. The exact rank-one asymptotic constant.

The escape-tube universal upper comparison is reproduced with a proof and attributed to the inspected earlier ProveIt package.

The manuscript was reviewed against the following potential failure points: circular endpoint conventions; the direction of the one-sided boundary; uniqueness in first-constraint cells; modular unwrapping; CRT coprimality; all residue-sign patterns, including empty cells; positive lengths rather than isolated points; component merging on finite grids; prime-modulus versus auxiliary composite-modulus roles; the order of the T and p limits; radius quantifiers; retained strict inequalities in deletion witnesses; total-variation normalization; and the distinction between unrestricted and progression-free testing functions.

## Executed exact checks

Command:

```sh
python3 code/verify.py --output verification.json --certificates arc_certificates.json
```

Result: **all exact checks passed**.

Ten explicit models were checked, including defining ranks 2, 3, 4, 5, 6 and 8. Exact integer/rational checks cover the parameter identities, CRT points, every listed arc, disjointness and gaps, independent interval sums versus the closed mass formula, both endpoints of the radius window, strict deletion witnesses, and the finite-prime ratio bounds.

Independent full enumeration of prime cyclic groups checked:

| rank | T | prime p | cardinality | one-sided boundary |
|---:|---:|---:|---:|---:|
| 2 | 10 | 10,007 | 105 | 3 |
| 3 | 17 | 1,000,003 | 261 | 7 |

Total prime-grid points exhaustively checked: **1,010,010**.

An independent interval-intersection routine examined **1,486** first-constraint cells over six small models, including every empty cell in those models.

Additional exact regressions:

- **990** nonzero-boundary instances of the attributed escape inequality.
- **2,976** rank-one instances of the exact interval boundary and its upper bound.
- **10,647** rational probability-measure/translation instances of the total-variation identity and finite tradeoff.

The larger prime-grid examples are not exhaustively enumerated. Their exact cardinalities are sums of rational endpoint floor/ceiling counts. The implemented Lucas–Lehmer test passed for Mersenne exponents **31, 61, 127, 521**; the two exhaustively enumerated primes were checked by trial division. The main mathematical theorem is for all sufficiently large primes and does not depend on these chosen primes or a new primality claim.

`arc_certificates.json` records every rational arc endpoint and its exact large-grid count. `verification.json` records the arithmetic results; `verification-run.txt` records the executed console output. Decimal ratios are explicitly labeled display-only and are not used to accept a test.

## What was not verified

No Lean files were compiled for this package, and no new theorem is claimed to be Lean verified. The full ProveIt audit and the complete OpenAI progression manuscript were not independently rebuilt or verified. The tests do not prove universal novelty, establish the sharp rank-r constant for r >= 2, or solve the fixed-radius-uniform-in-rank problem. Ordinary proofs of the infinite families are in `article.tex`/`article.pdf`; tests are not substituted for those proofs.

## Reproducibility and document checks

A second execution under `python3 -O` passed and produced byte-identical `verification.json` and `arc_certificates.json` files. The final 18-page PDF was compiled with three successful pdfLaTeX passes. The final LaTeX log contained no warnings, overfull boxes, underfull boxes or errors. All 18 pages were rendered with Poppler and visually inspected in contact sheets, with title, contents, numerical table and references also inspected at full-page scale. No clipping or broken mathematical glyphs was observed.
