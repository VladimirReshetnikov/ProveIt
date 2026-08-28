# Exponent-Sequence and Newton-Basis Frontiers for the Fabius-Rvachev System

This archived companion directory preserves the code, figures, and data from
the former 34-page frontier report prepared from the recursive LaTeX corpus
under:

`Analysis/FabiusFunction/docs`

in Vladimir Reshetnikov's `ProveIt` repository, pinned at commit:

`32d6d36c51d803289e6d6a0dc0c37753766eba47` (27 August 2026).

The audit inventory in Appendix A contains all 67 distinct `*.tex` paths in that
snapshot. Historical revisions are treated as mathematical lineages rather than
as independent claims; current descendants and distinctive archived material set
the non-duplication boundary.

The report itself is now incorporated into the consolidated source and PDF two
levels above this directory.

## Contents

- `../../Exponents_and_q_Series_Frontiers.tex` - consolidated LaTeX source.
- `../../Exponents_and_q_Series_Frontiers.pdf` - consolidated rendered report.
- `numerical_experiments.py` - fully commented, deterministic numerical checks.
- `requirements.txt` - Python package versions used for the supplied results.
- `figures/` - the two figures embedded in the report.
- `data/` - signed q-Richardson errors, boundary-layer errors, zero
  multiplicities, and the verification log.
- `SHA256SUMS` - checksums for the report, source, code, figures, and data.

No Monte Carlo sampling is used. The boundary profiles are obtained by FFT
inversion of exact characteristic products, while the q-Richardson identities
are checked at 100-decimal-digit precision.

## Rebuild the PDF

A TeX Live installation containing Libertinus, `latexmk`, `amsmath`, `booktabs`,
`longtable`, `tabularx`, `cleveref`, `hyperref`, and `listings` is sufficient.
The report was built with TeX Live 2025/dev, pdfTeX 1.40.26, and latexmk 4.86.

From this companion directory:

```bash
cd ../..
pdflatex -interaction=nonstopmode -halt-on-error Exponents_and_q_Series_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Exponents_and_q_Series_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Exponents_and_q_Series_Frontiers.tex
```

The source falls back to Latin Modern if Libertinus is unavailable.

The title pin remains the report's historical audit snapshot.  Its explicit
post-snapshot note records that the denominator-free geometric principal
specialization and all residual moments are formalized at Lean checkpoint
`1e761ed77583e9870ceeaeb2c74ac824094f0f3f`; the report's analytic remainder,
tomography, and exponent-sequence claims retain their stated frontier status.

## Reproduce the numerical experiments

The supplied outputs were generated with Python 3.13.5 and the package versions
recorded in `requirements.txt`.

```bash
python -m venv .venv
. .venv/bin/activate                 # Windows PowerShell: .venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
python numerical_experiments.py --output-dir reproduced
```

The command performs all exact/high-precision assertions before writing any
headline results. To compare with the packaged output:

```bash
cmp data/verification_log.txt reproduced/verification_log.txt
cmp data/richardson_tomography.csv reproduced/richardson_tomography.csv
cmp data/boundary_layer_errors.csv reproduced/boundary_layer_errors.csv
cmp data/zero_multiplicities_d2.csv reproduced/zero_multiplicities_d2.csv
```

On Windows, `Compare-Object` or `fc.exe` can be used in place of `cmp`.

## Main result families

The report develops a universal dyadic exponent-sequence construction

`Phi_a(z) = product_h sinc(z/2^h)^(a_h)`

and shows that the same generating function `A(q)=sum_h a_h q^h` controls the
random-series law, support, integer-zero divisor, spectral zeta function,
2-automatic lobe signs, Prouhet cancellation, even cumulants, q-Richardson
reconstruction, finite refinement rank, Mellin endpoint poles, and leading
Lambert-W inversion.

The principal concrete specialization is the even-degree alternating Newton
family `a_h = binom(h-1,d)`. It gives positive-definite entire quotients of the
Pascal-Rvachev hierarchy; for `d=2`, the characteristic function is
`Phi_1 Phi_3 / Phi_2`, despite the negative exponent in that factorization.
