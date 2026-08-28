# Assets for Part II of Representation Frontiers

These files support Part II of the consolidated volume
[`../../Representation_Frontiers.tex`](../../Representation_Frontiers.tex):

**Representation Atlas and New Analytic Bridges for the Fabius Function, Rvachev's Up-Function, and Their Fourier Images**

The former standalone TeX/PDF pair was absorbed into the volume and is
available through git history. The underlying report was prepared on 27 August
2026 from a recursive audit of the LaTeX corpus under
`Analysis/FabiusFunction/docs`.

## Package contents

- `numerical_experiments.py` -- fully commented, deterministic numerical checks.
- `figures/gamma_factorization_convergence.png` -- dyadic-gamma factorization check.
- `figures/jensen_mean_comparison.png` -- exact versus numerical Jensen circular mean.
- `figures/gaussian_mixture_characteristic_function.png` -- two simulations of the logistic/Gaussian-mixture duality.
- `figures/fabius_sine_series_convergence.png` -- convergence of the odd-harmonic Fabius series.
- `figures/numerical_results.txt` -- plain-text numerical audit trail.
- `SOURCE_AUDIT.md` -- source boundary, deduplication method, collision quarantine, and novelty status.

## Source snapshot

The primary formal exposition is pinned to repository commit

`0770442945d65bac5530c4f214c6c52c4cb9fbdc`

at

`https://github.com/VladimirReshetnikov/ProveIt/tree/0770442945d65bac5530c4f214c6c52c4cb9fbdc/Analysis/FabiusFunction`

The living draft tree was also audited because it contains results not yet consolidated into the primary exposition. Historical archive copies were deduplicated using the repository's provenance map; living successors were reviewed instead of counting renamed or byte-identical copies as independent sources.

## Status vocabulary in the report

- **[repository] / [repo]** -- explicitly present in the audited source corpus.
- **[derived synthesis] / [derived]** -- a direct consequence or recombination of audited results, included for completeness but not claimed as a new theorem.
- **[proved here] / [new]** -- proved in the report and not found by targeted formula and concept searches in the audited corpus.
- **[conjecture]** -- a clearly marked unproved statement or research target.

“Proved here” is deliberately a **new-to-the-audited-corpus** designation. It is not a universal claim of priority over all published or unpublished literature.

## Principal new theorem packages

The report develops five main bridges:

1. A meromorphic dyadic gamma function
   `Gamma_dy(z) = product_{h>=0} Gamma(1 + z/2^h)`
   with Mahler equation, arithmetic pole divisor, canonical reciprocal product, heat-trace integral, and the reflection factorization
   `Phi(z) = 1/(Gamma_dy(z) Gamma_dy(-z))`.
2. Equality in law between the existing dyadic logistic series and a Gaussian variance mixture driven by the existing discrete-Thorin gamma convolution, together with a convolution semigroup and an explicit Levy density.
3. An exact Jensen circular mean for `log|Phi|`, including a finite factorial product and recovery of the binary digit sum from its radial derivative.
4. A proof that the Rvachev Fourier image and its dyadic gamma factors are not D-finite, using their unbounded arithmetic zero multiplicities.
5. Distributional and compact Fourier representations of the bounded Fabius CDF, an odd-harmonic sine series for `F`, and nonlinear Fourier/sine-series representations for the inverse Fabius function.

The report also assembles a broad atlas of established probability, convolution, spline, product, sampling, Mellin, Laplace, moment, q-series, Lambert-W, and inverse-function representations.

## Reproducing the numerical experiments

Requirements:

- Python 3.10 or newer
- NumPy
- SciPy
- Matplotlib

From this asset directory, run:

```bash
python numerical_experiments.py
```

To write results elsewhere:

```bash
python numerical_experiments.py --output-dir path/to/output
```

The script uses the fixed random seed `20260827`, performs no network access, and overwrites the four figures and `numerical_results.txt` in the selected output directory.

The included run used 100,000 samples for each stochastic construction. Its headline checks were:

- dyadic-gamma factorization errors between approximately `1.8e-15` and `3.6e-15`;
- maximum Jensen mean discrepancy approximately `7.1e-15` on 76 test radii;
- two-sample KS statistic `3.47e-3` with p-value `0.5825` for the two simulated dual laws;
- agreement of the 128-term Fabius sine series with independent Fourier quadrature at roughly `1e-12` to `7e-12` on the reported test set.

See `figures/numerical_results.txt` for all recorded values and truncation diagnostics.

## Compiling the report

A standard TeX Live installation with the packages named in the consolidated
preamble is sufficient. From this asset directory, build the canonical source
with exactly three passes:

```bash
cd ../..
pdflatex -interaction=nonstopmode -halt-on-error Representation_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Representation_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Representation_Frontiers.tex
```

The consolidated source contains the exact relocated figure paths.

## Validation boundary

The original standalone build record remains available in git history. Current
font, reference, page-count, and rendering checks apply to the consolidated PDF
beside `Representation_Frontiers.tex`, not to a deleted standalone PDF.
