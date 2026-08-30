# Confluent Digital Extrapolation and Lambert-Phase Tomography

This supporting-asset bundle contains the reproducible numerical experiments and generated
data for a frontier report on the Fabius--Rvachev--Thue--Morse system. The report is now
displayed as Part VI of
[`../../Frontier_Compilations.tex`](../../Frontier_Compilations.tex).

## Corpus boundary

The nonduplication audit is pinned to the immutable repository snapshot

- repository: `VladimirReshetnikov/ProveIt`
- commit: `f49aad5c9c6d627a64822ea9f8e46f5270b95cef`
- subtree: `Analysis/FabiusFunction/docs`
- recursive docs-tree SHA: `6063d0d90cd9a4d25ca74cd4f8b80448313fce64`
- LaTeX paths in that subtree: 78

`corpus_manifest.txt` gives the complete path inventory. Historical revisions were treated
as mathematical lineages: a corrected successor supersedes an older normalization, but a
result surviving only in an archived source still counts as prior art.

The word *new* in the report always means *not found as the same theorem or construction in
this pinned corpus*. It is not a claim of worldwide publication priority.

## Main report results

The report proves four interconnected theorem families.

1. **Confluent geometric annihilation.** A normalized shift polynomial with a root of
   multiplicity `m` at `q` annihilates every mode `n^ell q^n` with `ell < m`. The report
   derives the unique shortest filter, its exact coefficient norm, mixed-mode extension,
   and a Banach-valued remainder theorem.
2. **Bounded digital filters.** A twisted length-`2^m` Thue--Morse polynomial has order-`m`
   confluence at `q`, while its `l1` condition number remains bounded as `m -> infinity`.
   This yields an explicit stability-versus-span tradeoff and a minimal-span theorem for
   collision-free subset factorizations.
3. **Rational Lambert-phase orbits.** Exact multiplicative phase locks in the coordinate
   `x = lambda 2^{-lambda}` turn inverse powers and logarithmically decorated inverse powers
   into ordinary and confluent geometric modes. This gives stable endpoint coefficient
   extraction with bounded geometric Richardson weights.
4. **Maximal-strip tomography.** The known Gamma--zeta Fourier coefficients imply an exact
   maximal holomorphy strip of half-width `pi/(2 log 2)`. Weighted Wiener/Bell estimates and
   phase-grid DFT alias formulas lead to a certified radial--angular recovery scheme for
   periodic endpoint coefficients.

Natural-boundary behavior, sharp alias asymptotics, optimal span/conditioning tradeoffs,
irrational near-locks, higher-rank strip widths, and late Bell-coefficient resurgence are
stated separately as conjectures or research programs.

## Files

- `numerical_experiments.py` -- extensively commented exact and high-precision checks.
- `corpus_manifest.txt` -- complete 78-path audit boundary.
- `experiment_results.txt` -- compact human-readable verification summary.
- `verification.json` -- machine-readable headline checks.
- `filter_conditioning.csv`, `conditioning_tradeoff.png` -- minimal versus digital filters.
- `lambert_conditioning.csv`, `lambert_conditioning.png` -- additive versus multiplicative
  phase-lock conditioning.
- `gamma_zeta_coefficients.csv`, `gamma_zeta_decay.png` -- endpoint Fourier coefficient decay.
- `tomography_errors.csv`, `tomography_errors.png` -- controlled radial--angular experiment.
- `requirements.txt` -- Python dependencies.
- `SHA256SUMS` -- checksums for the retained supporting files.

## Reproduction

Use Python 3.10 or newer:

```bash
python -m pip install -r requirements.txt
python numerical_experiments.py --output-dir . --precision 90
```

Rebuild the consolidated paper from this asset directory with the
repository-required three passes:

```bash
cd ../..
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
rm -f *.aux *.log *.out *.toc
```

The canonical output is
[`../../Frontier_Compilations.pdf`](../../Frontier_Compilations.pdf). The original
standalone build used Python 3.13.5, mpmath 1.3.0, NumPy 2.3.5, Matplotlib 3.10.8,
latexmk 4.86, and pdfTeX 1.40.26.

## Numerical-status note

The cancellation and normalization checks use `fractions.Fraction`; zero residuals are exact,
not tolerance tests. Gamma--zeta coefficients use arbitrary-precision `mpmath` arithmetic.
In the tomography experiment, the leading periodic function `A_0` is the actual Gamma--zeta
series from the endpoint theory. Higher coefficient functions `A_j`, `j >= 1`, are explicitly
documented smooth surrogates used to test the new sampling/filter algebra; they are not
presented as the true Fabius endpoint coefficients.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Frontier_Compilations.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
