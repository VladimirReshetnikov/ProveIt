# Global Fueter Primitives, Affine Monodromy, and Spherical Singularities

**A two-period range theorem and a rational–logarithmic classification**  
Research manuscript, 21 September 2026. 21 pages.

## Contents

- `global_fueter_primitives.pdf`: the complete typeset article.
- `global_fueter_primitives.tex`: standalone LaTeX source, including references.
- `verify_formulas.py`: symbolic differential-identity checks and numerical
  contour-period checks.
- `verification_results.json`: results of the supplied checks.
- `requirements.txt`: Python packages used by the checks.
- `Makefile`: convenience commands for compiling and checking.

The article develops the local inverse-Fueter construction in the supplied
`quaternionic_analysis.tex`; the original attachment is not required to compile
or understand the new article.

## Main mathematical results

1. A necessary-and-sufficient global inverse criterion using two closed
   quaternion-valued forms, with explicit reconstruction and affine monodromy.
2. A split finite-dimensional range obstruction: real dimension 8h for a product
   domain with h independent planar holes. For reflection-symmetric slice
   domains, only conjugate pairs of nonreal holes contribute.
3. A unique local finite-growth normal form at a nonreal singular sphere:
   transverse growth O(rho^(-m)), modulo extendible fields, has real dimension
   8m. Uniform o(rho^(-1)) growth is removable, and the threshold is sharp.
4. A global rational–logarithmic classification for finitely many nonreal
   singular spheres with polynomial growth at infinity, together with an exact
   dimension formula.

The article states the domain, symmetry, regularity, finite-topology, and growth
hypotheses precisely. The spherical classifications concern **axially
monogenic** functions; they are not classifications of all Fueter-regular
functions. Nonreal spherical singularities are not real-point singularities.

## Scientific status

These are proposed research results, accompanied by detailed analytic proofs.
They have not been peer reviewed or formally verified. A targeted primary-source
search did not locate the exact global range and singularity classifications;
this is not a certification that equivalent theorems have never appeared.

The local inverse, affine kernel, and related arctangent kernels are established
results and are credited. The literature comparison includes the August 2026
revision of Colombo–De Martino–Sabadini's Taylor/Laurent-series manuscript.
No classical named open conjecture is claimed to have been settled.

## Build the PDF

A standard TeX Live installation with the packages named in the preamble is
required, including `newtxtext`, `newtxmath`, `amsmath`, `amsthm`, `mathtools`,
`geometry`, `microtype`, `hyperref`, and `bookmark`.

```sh
pdflatex -interaction=nonstopmode -halt-on-error global_fueter_primitives.tex
pdflatex -interaction=nonstopmode -halt-on-error global_fueter_primitives.tex
```

Alternatively, run `make`. References are embedded in the source; no BibTeX run,
external figures, network access, or separate font files are required.

## Run the supplementary checks

Use Python 3.10 or later:

```sh
python -m pip install -r requirements.txt
python verify_formulas.py
```

The script writes `verification_results.json` and exits with an error if any
check fails. It checks nine exact symbolic identities and twelve numerical
contour-period pairs, including ordinary and reflection-compatible logarithmic
defects. All supplied checks passed; the largest numerical period error was
approximately 2.22e-16 in the recorded run. Results may vary slightly by platform.

These finite diagnostics test formulas, signs, and normalizations. They do not
prove global existence, uniqueness, removability, completeness, or novelty. The
article's analytic arguments, not the numerical tests, support those claims.
