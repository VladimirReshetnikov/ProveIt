# Polylogarithm Order Jets and Resonant Inversion

A comprehensive research report prepared for Vladimir Reshetnikov on the intersection of the ProveIt polylogarithm and transseries programmes.

**Version:** 1.0, 12 October 2026  
**Inspected ProveIt commit:** `9ec0f0406afe7a5475b03ff65ed91f7e283979b8`

## Start here

- `polylogarithm_order_jets.pdf` — the complete article, including all proofs, a source audit, quantitative verification tables, ten research questions, and references.
- `polylogarithm_order_jets.tex` — one complete LaTeX source. Its figure is supplied in `figures/`.
- `CLAIMS.md` — statement-by-statement proof status, hypotheses, attribution, and limitations.
- `INTEGRATION.md` — exact predecessor paths and proposed crosslinks for later integration.

The manuscript proves:

1. A fixed-sheet complex-sector extension of the repository's uniform all-integer resonance theorem.
2. A finite reciprocal-Gamma transformation from Lerch/polylogarithm order derivatives to pure logarithmic normal forms.
3. Convergent Lambert-coordinate inverse charts at arbitrary positive integer logarithmic degree, explicit all-order inverse coefficients, and sharp Catalan pole constants.
4. Common analytic charts for critical points and critical values near order two, local exhaustion of the small imaginary-order principal-sheet critical lattice, exact inverse branch splitting, and an analytic fold.
5. Exact Borel completion and integer-order-jet reconstruction, a meromorphic cosecant kernel, and a convergent expansion through every exponential sector of the integer-order inverse.
6. An order/logarithm crossover in the revived factorial coefficients.

The proofs are conventional analytic proofs with finite symbolic and high-precision numerical diagnostics. The numerical checks are not interval certificates or machine-formalized proofs. Historical priority has not been established by an exhaustive literature review; the article attributes classical inputs and identifies sources requiring further comparison.

## Build the PDF

From this directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error polylogarithm_order_jets.tex
```

Or run `make pdf`. A standard TeX Live installation with pdfLaTeX, Latin Modern, amsmath/amsthm, mathtools, microtype, booktabs, fancyhdr, hyperref, and cleveref is sufficient. No BibTeX run, network access, or repository checkout is required. The delivered PDF was built with TeX Live 2023 and latexmk 4.83.

## Reproduce the checks

The recorded output is preserved in `data/`. Install the Python packages into an environment of your choice:

```bash
python3 -m pip install -r requirements.txt
python3 code/run_checks.py
```

The default output directory is `verification_run/`, so reproduction does not overwrite the supplied records. The complex-order program uses 220 decimal digits and takes appreciably longer than the other checks. Select individual programs with, for example:

```bash
python3 code/run_checks.py --only local borel
python3 code/run_checks.py --only complex principal
```

Direct invocations are also supported:

```bash
python3 code/verify_local_jets.py --output verification_run/verification_local_jets.json
python3 code/verify_borel_jets.py --output verification_run/borel_verification.json
python3 code/verify_complex_resonance.py --output verification_run/complex_resonance_checks.json
python3 code/verify_principal_sheet.py --output verification_run/principal_sheet_check.json
```

Create `verification_run/` first when using the direct commands. The wrapper creates it automatically.

### Recorded evidence

| Program | Scope |
|---|---|
| `verify_local_jets.py` | 171 exact finite symbolic cases; four complex-argument defining-series comparisons; two inverse diagnostics |
| `verify_borel_jets.py` | 99 exact finite symbolic cases; four independent first-jet integral comparisons |
| `verify_complex_resonance.py` | Nine critical-lattice samples, eighteen split-root samples, twelve unfolded-root samples |
| `verify_principal_sheet.py` | One independent Bose-integral diagnostic at a principal-sheet zero, with analytic integration-cutoff bounds |

Thus the package records 270 finite symbolic cases and 50 numerical examples/diagnostics across the four programs. Counts refer to parameter cases, not every intermediate arithmetic comparison.

The local inverse and jet checks use actual logarithmically weighted defining sums. The Borel reference uses a logistic-density integral. The extra principal-sheet diagnostic uses a real Bose integral and records `Re(t)>0` and `|exp(-t)|<1`. Analytic cutoff bounds in that last program do not certify quadrature rounding.

## Reproduce the figure

```bash
python3 code/plot_complex_resonance.py --data data/complex_resonance_checks.json --output-dir figures
```

The figure contains measured points from the JSON and reference laws with analytically computed coefficients; there are no fitted reference constants. Appendix A derives the third split-root coefficient used in the second error curve. The PDF figure is vector-based; the PNG is a preview alternative.

## Source and correction audit

No new error was confirmed in the repository predecessor theorems directly used here. The article proposes an explicit extension of the real-axis resonance result and documents two external scope corrections:

- The modulus calculation behind a fixed-order boundary-accumulation claim in Vepstas's 2023 draft.
- The unqualified principal-branch finiteness statement in §8.1 of the inspected author-hosted version of O'Sullivan's *Zeros of the dilogarithm*. The small imaginary-order zero lattice supplies an exception. This does not affect the preceding positive-real-order theorem, and no error is attributed to the inaccessible original Gawronski theorem cited by the overview.

See the proofs, precise source locations, and limitations in the article and `CLAIMS.md`. No repository files have been modified.

## Package contents and provenance

- `code/`: four mathematical verification programs, a reproduction wrapper, and the plotting program.
- `data/`: the original recorded verification results.
- `figures/`: vector PDF and PNG of the research figure.
- `provenance.json`: repository snapshot, source roles, review boundaries, and runtime versions.
- `BUILD_VERIFICATION.json`: final PDF, visual review, and reproduction checks.
- `SHA256SUMS`: checksums of the deliverable files.

The article contains the complete deliverable; the source package includes no downloaded copies of third-party papers or of the ProveIt repository. The exact source links and pinned predecessor paths support later review and integration.

After extraction, run `sha256sum -c SHA256SUMS` from this directory to verify the supplied files before rebuilding or regenerating results.
