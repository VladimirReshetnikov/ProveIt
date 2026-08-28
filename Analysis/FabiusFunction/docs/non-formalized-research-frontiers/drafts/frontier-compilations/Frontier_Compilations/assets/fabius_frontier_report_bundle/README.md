# Confluent Digital Extrapolation and Lambert-Phase Tomography

This retained companion directory preserves the reproducible numerical experiments and
generated data for source report VI of the consolidated Fabius--Rvachev--Thue--Morse
frontier volume. The formerly standalone manuscript now appears in
`../../Frontier_Compilations.tex`, and its rendered PDF is
`../../Frontier_Compilations.pdf`. Those volume files are referenced rather than duplicated
here. Other paths below are relative to this companion directory unless stated otherwise.

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

## Retained companion files

- `../../Frontier_Compilations.tex` -- source of the consolidated volume containing this report.
- `../../Frontier_Compilations.pdf` -- rendered consolidated volume.
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
- `SHA256SUMS` -- checksums for the retained files.

## Reproduction

Use Python 3.10 or newer:

```bash
python -m pip install -r requirements.txt
python numerical_experiments.py --output-dir . --precision 90
```

From this retained companion directory, rebuild the consolidated paper with
exactly three serial `pdflatex` passes:

```bash
cd ../..
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
pdflatex -interaction=nonstopmode -halt-on-error Frontier_Compilations.tex
```

These commands rebuild `../../Frontier_Compilations.pdf`. The archived computation used
Python 3.13.5, mpmath 1.3.0, NumPy 2.3.5, and Matplotlib 3.10.8. The consolidated
manuscript uses the Libertinus Type 1 package when available and falls back to Latin Modern.

## Numerical-status note

The cancellation and normalization checks use `fractions.Fraction`; zero residuals are exact,
not tolerance tests. Gamma--zeta coefficients use arbitrary-precision `mpmath` arithmetic.
In the tomography experiment, the leading periodic function `A_0` is the actual Gamma--zeta
series from the endpoint theory. Higher coefficient functions `A_j`, `j >= 1`, are explicitly
documented smooth surrogates used to test the new sampling/filter algebra; they are not
presented as the true Fabius endpoint coefficients.
