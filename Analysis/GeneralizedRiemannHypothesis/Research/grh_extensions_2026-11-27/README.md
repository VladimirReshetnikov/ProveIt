# Two extensions of the ProveIt GRH development

Prepared for Vladimir Reshetnikov, 27 November 2026.

## Read first

`report.pdf` is the complete paper, **Unsmoothed prime fluctuations and information loss in symplectic projections**. Its source is `report.tex`, the three files under `sections/`, and `references.bib`.

The paper proves two extensions of the supplied article:

1. **Unsmoothed multiscale prime fluctuations.** Using Dirichlet GRH as the arithmetic input, the correctly centered ordinary prime-counting errors at any finite set of distinct multiplicative scales have positive definite covariance. This survives arbitrary finite deletion of zero frequencies, and every real unit direction has positive and negative excursions on a positive fraction of every sufficiently long logarithmic interval. No simplicity or linear independence of zero ordinates is assumed.
2. **Symplectic information loss.** For an n by (n+c) Lagrangian projection with a nondegenerate source form, full matrix laws become almost perfectly distinguishable while rank laws become almost identical. The paper proves exact laws, uniform asymptotics including n=c, and the sharp rank-only sample scale q^(2n-c).

The arithmetic theorem answers the multiscale unsmoothed-count clause of item 10 in the article's `zer:sec:open`. The matrix theorem develops a growing-dimensional family within `spn:q:symplectic`. The exact rectangular likelihood specializes the article's existing general count; the new statistical asymptotics are explicitly distinguished from that earlier result. See `provenance/NOVELTY_SCOPE.md` for the limited external-priority claim.

## Contents

- `report.pdf`: complete proofs, source analysis, numerical table, and formalization route.
- `report.tex`, `sections/*.tex`, `references.bib`, `report.bbl`: all manuscript sources.
- `code/verify_symplectic.py`: standard-library Python program with actual finite-field enumeration and exact rational formula checks.
- `results/symplectic_validation.json`: exact fractions and decimal displays, including 313,170 enumerated frames and 11,295 individually checked matrices.
- `results/build_validation.json`: compilation, page, and visual-review status.
- `code/verify_source_snapshot.py`: verifies expected Git blob hashes against a local checkout.
- `provenance/source_snapshot.json`: full pinned commit identifiers and 44 inspected/materialized source-file hashes.
- `provenance/SOURCE_AUDIT.md`: exact scope of the static Lean source review.
- `provenance/INDEPENDENT_MATH_REVIEW.md`: mathematical check of the rectangular formulas.
- `provenance/PROOF_REVIEW.md`: internal review of both arguments and the independently rerun computations.
- `provenance/NOVELTY_SCOPE.md`: comparison with the source article and primary literature.
- `build.sh`: rebuilds the PDF using an ordinary TeX Live installation; includes a local fallback for the configuration encountered during preparation.
- `SHA256SUMS.txt`: checksums of the delivered files.

## Reproduce the computations

From this directory:

```bash
python3 code/verify_symplectic.py
```

Python 3 is the only dependency. The program exhaustively enumerates the listed small cases and uses `fractions.Fraction` for every finite probability identity. The quaternary examples use the field F_2[x]/(x^2+x+1), not integers modulo four. Decimal approximations of infinite products are illustrative; no infinite claim rests on those approximations.

The program rewrites the result JSON and records elapsed time, so rerunning it can change the result-file checksum without changing the mathematical results. The all-parameter proofs are in the paper.

## Rebuild the paper

```bash
bash build.sh
```

An ordinary installation can equivalently run `pdflatex report`, `bibtex report`, and `pdflatex report` twice. The paper uses standard LaTeX packages, Latin Modern fonts, and no downloaded images or external data.

## Verify the source version

Use a local checkout at ProveIt commit `3d8689ceae76501a5c50f67da37e85369aac4fb6`:

```bash
python3 code/verify_source_snapshot.py /path/to/ProveIt
```

This checks the manifest's file content hashes; it does not build Lean. The vendor identifies upstream `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`.

## Verification boundary

The paper's new results are proved in ordinary mathematics, not Lean. The upstream theorem statements and their relevant source paths were inspected, but the Lean build and reported independent proof replays were not rerun. The finite-field verification was run successfully during preparation. The PDF was compiled and visually checked. External priority for the complete new formulations remains unverified; this archive makes a specific, auditable novelty claim relative to the supplied article.
