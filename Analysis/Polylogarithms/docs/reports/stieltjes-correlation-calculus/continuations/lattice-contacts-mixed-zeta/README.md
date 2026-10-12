# Lattice Contacts and Mixed Zeta Identities

Research continuation prepared for Vladimir Reshetnikov's ProveIt project, 11 October 2026.

Source snapshot: 36edefa8c531d9d6df8306ac51bcc317250f404c.

## Read the article

Lattice_Contacts_and_Mixed_Zeta_Identities.pdf is the complete article.
Lattice_Contacts_and_Mixed_Zeta_Identities.tex is a standalone, directly compilable source with no local TeX dependencies.

For editing and integration, article.tex inputs preamble.tex, references.tex, and the eight source files in sections/. Those files produce the same article. The spectral source contains three separately numbered sections, so the finished article has ten numbered sections.

The article includes complete proofs, ordinary convergent specializations, exact coefficient certificates, a source-status correction, and twelve consolidated research questions.

## Principal results

1. Every contact polynomial at a minimally compensated nonpositive even Hurwitz order, with exact dependence on the cutoff coordinate.
2. An all-derivative periodic-filter criterion: zero mean removes every critical contact.
3. Exact modular transport of the Lambert order family near nonpositive even orders and order one, with complete nonmodular contour corrections.
4. A polarized Bernoulli recurrence for arbitrary products of unequal even-order Hurwitz tails and every regular centered moment.
5. Explicit mixed cubic and quartic generators, six- and eight-coordinate reconstruction certificates, two short ordinary identities, and a finite cubic telescoper.
6. A jointly holomorphic generator for independently shifted generalized Stieltjes products, including every argument derivative and a concrete gamma_1 times digamma identity.
7. All polynomial spectral-face coefficients, all logarithmic weighted coefficients by a rational finite-difference formula, and a depth-two polylogarithm evaluation for every Gamma face with one displaced mass.
8. The complete independent-order polar obstruction and a holomorphic mixed-defect formula after explicit local subtraction.

Novelty is assessed against the inspected ProveIt corpus and specified primary literature. Classical anchors and special cases are explicitly credited. The Gaussian S6/revised S8 identities and the general unequal bilinear optimal-prefix conjecture remain open.

## Build

Python 3.10 or newer and a standard pdfLaTeX installation are sufficient. The tested environment used TeX Live 2023/Debian and latexmk 4.83. The TeX packages are standard AMS, mathtools, mathrsfs, Latin Modern, microtype, geometry, booktabs, longtable, enumitem, fancyhdr, hyperref, and bookmark.

From this directory:

    python3 build.py

This assembles the standalone TeX from the modular files and compiles its PDF. It rejects a build with overfull boxes or unresolved references. The build log is retained under build/.

Alternatively, compile the standalone TeX directly with pdfLaTeX three times, or compile article.tex with latexmk.

## Replay verification

Install the optional numerical dependencies:

    python3 -m pip install -r requirements.txt

Run all six programs:

    python3 run_checks.py

The full numerical suite can take several minutes. It rewrites the result JSON files under results/. No network access is used by the verification programs.

The exact mixed-tail suite uses only the Python standard library:

    python3 run_checks.py --exact-mixed-only

The programs can also be run individually from any working directory. Their output locations are relative to their own installed directory.

## Contents

- sections/: all theorem statements, proofs, examples, and research questions.
- verification/: six independent exact/numerical verification programs.
- results/: recorded exact matrices, determinants, symbolic checks, and numerical residuals.
- provenance/source_receipts.json: pinned repository paths, Git blob hashes, and local SHA-256 receipts.
- provenance/claims.json: machine-readable claim and scope map.
- INTEGRATION.md: proposed repository placement, label prefixes, and the exact source-status correction.
- VALIDATION.md: verification methods and their limits.
- MANIFEST.sha256: checksums of the delivered files, excluding the manifest itself.

The numerical results are diagnostic comparisons, not interval certificates. The exact rational matrices prove formal-coordinate rank and reconstruction; they do not prove arithmetic independence of special-function constants. No Lean proof is claimed.

