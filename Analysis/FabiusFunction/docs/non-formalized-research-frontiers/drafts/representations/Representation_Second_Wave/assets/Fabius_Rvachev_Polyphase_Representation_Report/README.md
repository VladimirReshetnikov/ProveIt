# Polyphase, Operator, and Jump-Measure Representations of the Fabius-Rvachev System

This reproducibility bundle accompanies the 44-page research report prepared for Vladimir Reshetnikov.

## Source boundary

The repository audit is pinned to the exact `ProveIt` commit

```text
19ad531146cda7bc11a206827566db7f5753d5b3
```

The audit covered the recursive `Analysis/FabiusFunction/docs` TeX inventory, including the primary exposition, current frontier syntheses, thematic drafts, historical archive lineages, and corrected source papers. The report uses the following status convention:

- `K`: explicitly present in the audited corpus or a cited classical source.
- `D`: a short transform or specialization of established material.
- `N`: proved in the report and not located in the pinned TeX corpus.
- `C`: conjecture or open research direction.

`N` is a corpus-relative novelty statement, not a claim of worldwide publication priority.

## Main contents

The report develops, among other things:

1. A modular-scale or polyphase factorization
   `Phi(z) = product_{a=0}^{r-1} Psi_r(z/2^a)` and the corresponding convolution factorization of Rvachev's up-density.
2. Sparse-scale sinc, cosine, Gamma, canonical-zero, log-zeta, cumulant, Bell-polynomial, spectral-zeta, and determinant representations.
3. A roots-of-unity projector for Mellin poles and logarithmic-scale harmonics.
4. Multidimensional half-space-volume and hyperplane-section representations of the Fabius function and its inverse.
5. Finite sparse box splines whose derivative jumps and distributional derivatives recover signed and unsigned Thue-Morse blocks.
6. Exact Bell-Bernoulli formulas for every surviving signed power sum on the sparse knot set.
7. Infinite products of averaging operators and an infinite-order Bernoulli/zeta differential logarithm.
8. A twisted Poisson family, integer-zero slope series for the Fabius function, and analytic Thue-Morse formulas from odd zero slopes.
9. A factorization of binary Thue-Morse parity into overlapping base-`2^r` digit-parity characters.
10. Conjectures and proposed research programs on uniform deconvolution asymptotics, sparse Mellin harmonics, Lambert-W endpoint transseries, Radon algorithms, Jacobi asymptotics, twisted scale characters, general bases, arithmetic values, and Lean formalization.

## Files

- `fabius_rvachev_polyphase_representations.tex` - LaTeX source.
- `fabius_rvachev_polyphase_representations.pdf` - rendered 44-page A4 report.
- `numerical_experiments.py` - commented, deterministic numerical and exact-symbolic checks.
- `polyphase_product_checks.csv` - high-precision checks of the modular-scale product.
- `fourier_deconvolution_checks.csv` - high-precision checks of the finite signed-comb Fourier quotient.
- `power_sum_moment_checks.csv` - exact rational moment/power-sum checks.
- `polyphase_cumulant_checks.csv` - exact rational cumulant recombination checks.
- `operator_coefficients.csv` - exact coefficients of the averaging-operator logarithms.
- `polyphase_fourier_factors.png` and `.pdf` - product-factor visualization.
- `thue_morse_jump_comb.png` and `.pdf` - derivative-jump/atomic-comb visualization.
- `verification_log.txt` - concise execution log.
- `MANIFEST.sha256` - SHA-256 hashes of all other files in the bundle.

## Numerical verification summary

The script uses 90 decimal digits for numerical product checks and exact SymPy rationals for algebraic checks.

- 16 polyphase product rows; maximum residual `7.36364019795e-91`.
- 9 Fourier deconvolution rows; maximum residual `3.63470487147e-90`.
- 18 moment/power-sum rows; every exact difference is `0`.
- 24 cumulant-recombination rows; every exact difference is `0`.

These computations are independent checks of normalization and algebra. The report supplies proofs for the identities; numerical agreement is not used as a substitute for proof.

## Reproduce the computations

Requirements:

- Python 3.10 or later.
- `mpmath`, `sympy`, `numpy`, and `matplotlib`.

Run:

```bash
python numerical_experiments.py
```

The script has no network dependency, no random seed, and no numerical quadrature. It regenerates all CSV files, both figures in PNG/PDF form, and `verification_log.txt`.

## Rebuild the report

A reasonably complete TeX Live installation is sufficient. The source uses `article`, `geometry`, Libertinus (with Latin Modern fallback), `microtype`, AMS math packages, `booktabs`, `longtable`, `tabularx`, `graphicx`, `xcolor`, `enumitem`, `fancyhdr`, `titlesec`, `tcolorbox`, `listings`, `xurl`, `hyperref`, and `cleveref`.

Run:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  fabius_rvachev_polyphase_representations.tex
```

The included figures allow the PDF to be rebuilt without rerunning the Python script first.

## Integrity check

On a Unix-like shell:

```bash
sha256sum -c MANIFEST.sha256
```

The manifest intentionally does not hash itself.
