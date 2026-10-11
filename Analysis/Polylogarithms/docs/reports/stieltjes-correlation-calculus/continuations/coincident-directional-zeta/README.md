# Coincident Stieltjes Products and Directional Zeta Identities

Research continuation prepared for Vladimir Reshetnikov, 10 October 2026.

The complete article is available as:

- Coincident_Stieltjes_and_Directional_Zeta.pdf
- Coincident_Stieltjes_and_Directional_Zeta.tex — self-contained source
- article.tex and sections/ — modular source for integration

## Mathematical contents

The article proves a finite completion rule for coincident Stieltjes
products, its explicit cubic Tornheim realization, a complete contact
distribution generator, a necessary and sufficient coordinate-invariance
criterion, all normal spectral derivatives in several colored integer-order
families, quadratic Tornheim derivatives on arbitrary admissible rays, and
all principal Laurent coefficients and finite parts in a common-shift
harmonic family with two independently moving exponents.

The cubic digamma finite part is rigorously reduced to the third diagonal
Tornheim derivative. That derivative is not reduced further to ordinary
zeta constants. The current Gaussian S6 and S8 candidates remain
conjectural. Classical ingredients and inherited results are credited.
The article contains fourteen concrete proposed research directions.

## Build

Requirements: Python 3 and a pdfLaTeX installation with the standard AMS,
Latin Modern, microtype, geometry, booktabs, longtable, enumitem, xurl,
mathrsfs, fancyhdr, tocloft, and hyperref packages.

From the package directory:

    python build.py

The builder recursively flattens the modular source, compiles it three
times in an isolated temporary directory, checks the final log for
unresolved references, missing characters, and overfull boxes, then writes
the standalone source, PDF, and a build receipt. No bibliography processor
is needed.

The modular source can alternatively be built with:

    latexmk -pdf article.tex

## Reproduce the mathematical checks

Install the Python dependencies from requirements.txt. Then run:

    python code/run_all.py

Each script is also independently executable. Full harmonic Laurent
checks are the slowest part. Output is written into results/. Tests use
exact symbolic arithmetic where stated and mpmath for numerical
diagnostics. They are not interval certificates and are not the proof
of the parameter-uniform theorems.

The checks cover:

- finite residue and binomial formulas, obstruction ranks, and Stieltjes thresholds;
- full Gamma Fourier coefficients versus the canonical contact formula;
- partial fractions, rational generating functions, composition counts, and harmonic coefficients;
- independent Mellin quadratures for Gamma and weighted identities;
- independent Jonquiere/incomplete-Gamma continuation for Tornheim ray derivatives;
- direct Hurwitz-product quadrature versus the multivariate cubic kernel;
- local digamma quadrature versus the third diagonal Tornheim derivative;
- discrete Cauchy extraction of two-exponent harmonic Laurent coefficients;
- all-order Stieltjes primitive specializations;
- the exact S6 depth-three reduction and restricted-separator diagnostic.

## Integration and provenance

See integration/INTEGRATION.md and integration/claim_ledger.json for
the theorem boundaries, dependencies, and source placement.

The source revision is:

    dcd95baeb7c0e914b138bddef6829c5b1d52b726

The receipt in provenance/source_receipt.json records 704 verified Git
blob identities for the extracted source corpus. This is source-integrity
evidence, not an assertion that every source theorem was independently
audited.

The patch in integration/carry_forward_source_corrections.patch is
unapplied. It carries forward three previously identified corrections
still relevant at the pinned revision, and excludes an earlier PSLQ
wording correction already integrated. New corrections to the inspected
Borwein–Dilcher and Bailey–Borwein author PDFs are documented in the
article and the source audit, with exact replacements and derivations;
no claim is made about every published version.

No repository branch, manuscript source, or conjecture status was changed
in preparing this package.
