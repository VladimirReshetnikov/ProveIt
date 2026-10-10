# Nested Harmonic Jets and Gamma Renormalization

**Exact Stieltjes identities, regulator conversion, cyclotomic products, and all-depth polylogarithmic resonance**

Research continuation prepared for Vladimir Reshetnikov's ProveIt programme, 10 October 2026.

## Main article

`article.pdf` is the complete 23-page article. `article.tex` is its standalone source, including the bibliography. No external figure or bibliography files are needed to compile it.

The main results are:

- A holomorphic cutoff limit for nested harmonic products, with Gamma quotient at spectral order one, and a complete Bell-polynomial calculus of generalized Stieltjes constants and Hurwitz-zeta derivatives.
- An all-depth conversion from the specified harmonic regularization to diagonal Laurent finite parts. They already differ at depth two by `-gamma_1(a)`.
- The exact parameter-multiplication exponential and a higher-genus cyclotomic identity that reduces fractional-order products to ordinary Gamma ratios.
- A polylogarithmic Euler-primitive ladder and ordinary antiderivatives.
- A complete classification of polynomial truncations of the all-depth equal-order multiple-polylogarithm generator.
- An elementary formula for every first resonant spectral derivative, and an all-order Bell coefficient theorem reducing the r-th derivative to shifted logarithmic Euler sums of nesting depth at most r.
- Convergent endpoint cancellation identities, a targeted source audit, and twelve further research questions.

The derivative of `Li_{s,...,s}` always differentiates every order simultaneously along the diagonal. A moving depth weight and a fixed depth weight are different derivatives. The article proves and retains their correction term.

## Proof and novelty status

The article supplies ordinary analytic and algebraic proofs. It has not undergone independent peer review or proof-assistant verification. Classical Gamma products, symmetric-function identities, and established multiple-zeta regularization theory retain their attribution. No first-in-the-literature claim is made for every derived specialization.

This package does not settle the repository's remaining S6 or S8 candidates or numerical period independence. Its nesting-depth theorem is in an explicitly defined shifted-logarithmic-sum class, not a minimal-depth theorem for ordinary multiple polylogarithms.

## Provenance and integration

Pinned repository revision:

`fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed`

The source areas are `Analysis/Polylogarithms/docs/manuscript` and `docs/incoming`. The manuscript reading was targeted. The incoming inventory and README excerpts of its five archives were inspected, not their complete manuscripts and computational evidence. See `sources.json` and `integration/INTEGRATION_NOTES.md` for the exact scope and proposed placement.

No repository files were changed. The included editorial correction confirms a wording issue already noticed in incoming work; it is not presented as a new discovery.

## Build

A standard TeX Live installation with pdfLaTeX, Latin Modern, AMS packages, mathtools, geometry, microtype, booktabs, longtable, enumitem, xurl, fancyhdr, hyperref, and bookmark is sufficient.

```sh
python code/build.py
```

The helper compiles in a temporary directory, performs three passes, rejects unresolved references and overfull boxes, copies the resulting PDF to the package root, and writes `results/build_report.json`.

Alternatively, run pdfLaTeX three times directly on `article.tex`. `make pdf` calls the helper where Make and `python3` are available.

## Replay the verification

Tested with Python 3.13.5, SymPy 1.14.0 and mpmath 1.3.0.

```sh
python -m pip install -r requirements.txt
python code/run_checks.py
```

A quick run executes the exact algebra and higher-jet coefficient suites:

```sh
python code/run_checks.py --quick
```

Individual scripts can also be run directly. The full run takes roughly a minute on the preparation environment, but runtime varies. It rewrites the corresponding JSON results; the supplied outputs preserve the preparation run, and their checksums therefore change on replay.

| Script | Executed evidence |
|---|---|
| `code/verify_exact.py` | 826 exact finite assertions; also generates finite-part and resonance-polynomial tables. |
| `code/verify_numeric.py` | 99 whole-function, quadrature, product, and Cauchy finite-part comparisons at 60 decimal digits. |
| `code/verify_higher_jets.py` | 960 coefficient comparisons through spectral order four, using an independent recurrence and the Bell formula. |
| `code/verify_cyclotomic.py` | 16 higher-genus product comparisons at and near fractional resonances. |

The 1,075 numerical comparisons are arbitrary-precision floating-point diagnostics, **not interval certificates**. Numerical agreement is not the proof of the identities. `results/VERIFICATION_SUMMARY.md` explains the observed residuals and finite check coverage.

## Files

`article.tex`, `article.pdf`: main source and compiled article.

`code/`: reproducible verification and build helpers.

`results/`: executed outputs, exact formula tables, build metadata and PDF quality report.

`integration/`: placement guidance and the scoped editorial proposal.

`sources.json`: pinned source and primary-reference provenance.

`MANIFEST.sha256`: checksums of the delivered files, excluding this manifest itself. Rebuilding or rerunning verifiers changes some files; regenerate the manifest only when intentionally preparing a new delivery.
