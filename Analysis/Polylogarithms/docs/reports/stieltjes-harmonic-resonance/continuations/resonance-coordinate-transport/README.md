# Exact Resonance and Coordinate Transport

**Dougall–Hurwitz identities, nonlinear Stieltjes finite parts, and polylogarithmic correlations at unequal frequencies**

Research continuation prepared for Vladimir Reshetnikov, 10 October 2026.

The article gives analytic proofs answering three concrete questions in the current ProveIt incoming reports:

1. A fixed Dougall family with every nonpositive-integer resonance, an explicit residue polynomial, and complete spectral jets.
2. The exact nonlinear coordinate correction for Stieltjes finite parts, including composition and a sharp vanishing theorem.
3. Three unequal positive integer frequencies with disjoint singular grids, reduced to finitely many ordinary colored Tornheim kernels with the prescribed endpoint-scale terms.

The PDF has **39 pages**, nine sections, 22 numbered theorem/lemma/proposition/corollary statements, 15 bibliography entries, and 12 proposed research topics. Classical inputs and recovered identities are credited. The current Gaussian S6 and S8 evaluations remain conjectural.

## Main files

| File or directory | Purpose |
|---|---|
| Exact_Resonance_and_Coordinate_Transport.pdf | Complete article, with proofs, explicit identities, audit, and research agenda. |
| Exact_Resonance_and_Coordinate_Transport.tex | Complete standalone TeX source: preamble, every section, and bibliography. |
| article.tex, preamble.tex, sections/, references.tex | Matching modular sources for editing and integration. |
| build.py | Reassembles the standalone source and compiles it in three TeX passes. |
| code/ | Reproducible programs; see code/README.md for commands and reusable functions. |
| results/ | Recorded machine-readable verification outputs. |
| INTEGRATION_NOTES.md | Source-question crosswalk, proposed placement, and proof-status notes. |
| REVIEW_NOTES.md | Independent derivation and implementation checks from this research session. |
| provenance/source_manifest.json | Pinned source paths, source hashes, archive members, and crosswalk. |
| provenance/theorem_index.json | Numbered statements, source labels, and PDF pages. |
| results/document_validation.json | Final build and document checks. |
| requirements.txt | Tested Python dependency versions. |
| MANIFEST.sha256 | SHA-256 checksums for delivered files, excluding the manifest itself. |

The package contains no copied source repository or original incoming archives.

## Read the mathematics

| Statement | Article location |
|---|---|
| Centered finite subtraction, normal convergence, and derivatives | Theorem 2.2 |
| Uniform evaluation at every nonpositive integer resonance | Theorem 2.6, equation (2.15) |
| Every resonant Taylor coefficient in finite special-function data | Theorem 3.1, equation (3.4) |
| Weighted primitive and colored-polylogarithm counterterms | Section 4 |
| Universal nonlinear residue and exact composition | Theorems 5.1–5.2 |
| Finite coordinate coefficients for every Stieltjes derivative | Theorem 5.3 |
| Sharp vanishing at unit tangent when n ≥ 2r | Theorem 5.6 |
| All-index unequal-frequency finite-part reduction | Theorem 6.2 |
| Ordinary three-factor centered log-Gamma integral | Theorem 7.2 |
| Audit and evidentiary distinctions | Section 8 |
| Twelve further research questions | Section 9 |

The resonance series are ordinary convergent **bracketed differences**. Their counterterms remain inside the same summation. Finite parts use the stated right endpoint coordinate. Reciprocal-Gamma zeros are retained before spectral differentiation. These conventions are part of the statements.

## Build the article

From the extracted package directory:

    python3 build.py

The default engine is LuaLaTeX. A standard TeX Live installation needs the packages listed in preamble.tex, including Latin Modern, AMS mathematics, mathtools, microtype, geometry, booktabs, longtable, xurl, fancyhdr, hyperref, and bookmark. No external graphics, network access, BibTeX database, or shell escape is needed.

Temporary files go in .build/; the completed PDF is placed beside the standalone source. To reassemble TeX without compiling:

    python3 build.py --assemble-only

The standalone source can also be compiled directly in three passes:

    lualatex -interaction=nonstopmode -halt-on-error Exact_Resonance_and_Coordinate_Transport.tex
    lualatex -interaction=nonstopmode -halt-on-error Exact_Resonance_and_Coordinate_Transport.tex
    lualatex -interaction=nonstopmode -halt-on-error Exact_Resonance_and_Coordinate_Transport.tex

The delivered PDF was built with LuaTeX 1.17.0. The final build had no undefined references or citations, no package warnings, and no overfull or underfull boxes. All 39 pages were rendered for visual review. The optional --engine argument supports other installed LaTeX engines, but only the recorded LuaLaTeX build was used for the delivered PDF.

Edit the modular files first, then regenerate the standalone source. This avoids maintaining divergent copies.

## Reproduce the mathematical checks

Install the recorded Python dependencies, then run:

    python3 -m pip install -r requirements.txt
    python3 code/verify_all.py

The complete suite performs symbolic algebra and high-precision integration and may take several minutes. It runs the three main verifiers sequentially, streams their output, and stops on the first failure. Assertions remain enabled.

Recorded evidence:

- **Dougall:** finite exact coefficient checks and 19 numerical comparisons at 75 working digits. Largest observed absolute discrepancy: 3.76169e-36; acceptance threshold: 1e-31.
- **Nonlinear coordinates:** 138 finite symbolic cases plus 48 independent cutoff cases comprising 140 exact monomial pairings. The cutoff calculation uses inverse-Jacobian primitives independently of the proposed residue formula.
- **Unequal frequencies:** four exact piecewise polynomial integrals and 13 numerical comparisons at 45 working digits. An independent Bernoulli integral equals -1879/125411328 exactly.
- **Additional direct summation:** code/verify_dougall_direct.py reproduces the unaccelerated check of equation (3.28), independently of the asymptotic-tail evaluator. It is separate from the main suite.

These calculations check finite algebra, signs, normalizations, and implementations. Numerical outputs are **diagnostics, not interval enclosures**. The all-index claims are proved in the article. No proof-assistant formalization or external peer review is claimed.

## Source baseline and integration

The baseline is ProveIt commit:

    445f754610e1377939235794de84ed9075fc09f5

The requested manuscript directory and all five current incoming archive identities are recorded in the source manifest. The review is targeted: all 76 manuscript text files were retrieved, relevant passages and four principal incoming reports were examined, and the fifth report's scope and relevant audit/questions were checked. The manifest distinguishes retrieval from detailed inspection.

The proposed PSLQ wording correction is inherited from the Gauss–Hurwitz report and is credited there. No new false theorem was found in the selected premises. The existing S4 proof, the conjectural current S6/S8 candidates, and rejection of an older S8 vector retain their distinct statuses. This package is prepared for review and integration; it does not apply changes to the upstream repository.
