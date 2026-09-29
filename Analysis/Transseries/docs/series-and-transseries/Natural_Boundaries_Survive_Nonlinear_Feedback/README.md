# Natural Boundaries Survive Nonlinear Feedback

**Moving-parameter partial theta series, sharp half-plane realization, and the failure of angular Borel summation**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

`natural_boundaries_feedback.pdf` is the compiled 21-page A4 article.
`natural_boundaries_feedback.tex` is its standalone editable source, including the bibliography.

## Principal contribution

For every integer d >= 2, consider

    U_d(q) = sum_{j>=1} q^j exp(j^d U_d(q)).

The canonical actual inverse Q_d is holomorphic in a small left half-disc and smooth to its imaginary diameter. The article proves that **every point of that diameter is a natural boundary point**. Its locally univalent image is a curved natural boundary for the forward function U_d.

For d = 2, this supplies a negative answer to the angular-continuation question left open in ProveIt's `Negative_Ray_Summation_Exponential_Feedback` article. Both formal series have entire integrated Borel transforms and admit fine negative-ray summation, yet neither admits angular 1-summation in any open interval containing the negative direction.

The key proof is not a fixed-parameter gap theorem. It is an all-orders moving-curve moment estimate that excludes cancellation by an arbitrary holomorphic change of the geometric parameter. A mean-square argument handles tied closest poles.

The article also proves robustness under analytic forcing, periodic tail amplitudes and analytic finite-core changes, treats affine-quadratic exponents, and gives uniform closed-half-disc exponential-block error bounds for every d >= 2. Eight further research questions and a prospective formalization plan are included.

## Scope and limitations

These are conventional mathematical proofs, not Lean-verified results or independently peer-reviewed claims. The repository and literature review was targeted, not exhaustive; global publication priority is not asserted. The positive quadratic fine-summation result is credited to earlier work and reconstructed here, not presented as newly discovered.

For d >= 3, the local moving-curve noncancellation theorem uses the sufficient bound |q_0| < exp(-d). The implicit root is made small enough for this to hold. No globally optimal bound on q_0 is claimed.

The optimized truncation constant is derived from a positive majorant. It is not a matching lower bound for the actual signed error and is not a Stokes constant. The paper does not classify growth on every individual Borel ray or identify all higher-degree summation procedures.

## Build

A standard TeX Live installation with the packages listed in the preamble is sufficient. No repository checkout, external bibliography, image, font, or network access is needed.

```sh
sh build.sh
```

The build runs `pdflatex` three times and writes local build logs.

## Reproduce the checks

Python 3.10 or later is required. Exact checks use only its standard library.

```sh
python code/verify.py --order 24 --exact-only
python -m pip install -r requirements.txt
python code/verify.py --order 24 > data/run_output.txt
```

The recorded full run used Python 3.13.5 and mpmath 1.3.0. It passed 324 exact finite comparisons, ten moving-curve asymptotic diagnostics, four rational-boundary root calculations, 352 quadratic Fourier checks, and a tied-pole mean-square check. Numerical diagnostics used 110-digit working precision, not interval arithmetic.

Running the program replaces its own data files. An exact-only run marks numerical diagnostics as not run. The full run restores their recorded status. A small numerical residual must not be interpreted as a certified decimal enclosure.

## Package contents

- Article source and PDF.
- `code/verify.py`: independent formal, inverse, kernel, and tree-block constructions.
- `data/coefficients.csv`, `data/blocks.json`: exact finite output.
- `data/moving_curve_ratios.csv`, `data/boundary_points.csv`: floating-point diagnostics.
- `data/verification.json`, `data/run_output.txt`: actual execution records.
- `notes/proof_status.md`: proof dependencies, boundaries, and audit.
- `notes/provenance.json`: repository snapshot, reviewed sources, and primary literature.
- `notes/build_validation.json`: PDF build and visual-inspection record.

Repository snapshot: `ebd8344bca77d8352cd745b7df374618a290a029`. No upstream files were changed.
