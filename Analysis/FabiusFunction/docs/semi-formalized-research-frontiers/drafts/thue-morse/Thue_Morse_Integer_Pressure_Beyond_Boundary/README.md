# Positivity Beyond the First Thue Morse Feedback Boundary

This bundle contains the seven-page research report, editable LaTeX, exact mathematical checkers, and their saved results.

The report proves a fixed-offset asymptotic for H_(m,m+s), and positivity of both H_(m,m+s) and the degree-(4m+2s) pressure coefficient under either sufficient condition:

- m >= 800(s+1)^2
- m >= 2048 and 200(s+1) log(2m) <= m, with natural logarithm

The full proposed pressure range strictly below degree 6m remains open. These are ordinary mathematical results, not a Lean formalization or a priority claim.

## Verification

`python3 code/run_all.py` uses only the standard library. It checks exact cutoff inequalities, the saddle interval, 2,632 marked-pair profiles, 195 saved Schur pressure decompositions, and 35 saved restoration identities.

`python3 code/reproduce_all.py` requires SymPy. It reconstructs the rational Fourier matrices, checks every original linear-system residual and normalization, recomputes the Schur coefficients for m=2,...,14, and recomputes the deleted-insertion identities against the full nonlinear eigenvector recursion for m=2,...,8. The Schur pressure values are compared to the separately obtained direct phase-eigenvalue data in `data/direct_phase_reference.json`. The successful run is recorded in `data/full_replay.log`.

`python3 code/recompute_phase.py 2 3 4 5` optionally regenerates direct phase-eigenvalue pressure values. Pass additional moment orders through 14 for a larger independent replay. This is slower than the Schur recurrence.

The asymptotic and growing-strip theorems do not depend on a finite search. The scripts check exact identities and elementary side conditions used in the proof.

## Building the PDF

On a standard TeX installation run `make pdf`. The optional `build_local.sh` uses explicit paths for the Debian TeX installation used during preparation, creates only local build files, and runs two LaTeX passes.

The `background` folder preserves the pinned original pressure source and the preceding triangle/boundary LaTeX reports without edits. They supply the previously proved spectral normalization and strict tangent comparison. The new pressure proof uses the pre-feedback triangle plus the new offset-zero estimate, so it does not require replaying the earlier boundary's finite enclosure archive.

The final PDF is `article.pdf`; the main source is `article.tex`. Intermediate renderings and local TeX format files are excluded from the source archive.
