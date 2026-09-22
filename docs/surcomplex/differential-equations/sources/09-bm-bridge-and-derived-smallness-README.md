# Intrinsic Differential Calculus on the Surreal and Surcomplex Numbers

**Strong derivations, coherent analytic families, bounded phases, and linear differential equations**

A standalone, 23-page article prepared for the documentation of
`VladimirReshetnikov/Surreal`.

## The gap

The repository already has substantial analytic-variable calculus, finite-angle
trigonometry, algebra, foundations, and computation material. Its trigonometry
package explicitly declines to choose a derivation on `No` or to classify the
solutions of a differential equation. The article supplies the bridge from the
Berarducci–Mantova intrinsic derivation to those analytic and phase constructions.
This is a targeted documentation-scope audit, not an audit of all existing proofs.

The pinned repository commit is
`e260237db9b71da8b74a0c13c8e6355119091100`.
The commit identity was also checked against the GitHub commits endpoint.
See `REPOSITORY_SCOPE.md` and the article's embedded bibliography for provenance.
No repository files were modified or uploaded.

## Main contents

The paper distinguishes intrinsic differentiation of a number from differentiation
in a function variable and proves a total-derivative formula for common-domain
Hahn-coherent families. It constructs and analyzes the convex ideal of derivatives
of finite surreals, proves the exact logarithmic-derivative image theorem, and
identifies the maximal derivative-compatible exponential strip.

It then classifies the kernels of all complex constant-coefficient scalar
operators and all constant complex matrix systems; develops exact Laurent-series
resolvents with finite residual certificates; and proves a set-sized workspace
closure theorem. Throughout, ordinary convergence, Hahn summability, global
phase conventions, and differential compatibility remain separate notions.

The key first-order criterion is:

- A nonzero solution of `partial(y) = (a + i*b)*y` exists in `No[i]` exactly when
  `b` has a finite surreal primitive under the chosen derivation.
- This implies that `partial(y) = i*y` and `partial^2(y) + y = 0` have only the
  zero solution in this differential field. These are intrinsic differential
  equations, not equations for ordinary analytic functions of a free variable.

The BM existence theorem is an explicitly cited external input. Consequences are
proved in the article. No originality or priority claim is made, and no Lean
formalization or independent peer review is claimed.

## Files

- `article.tex` — complete standalone LaTeX source, with embedded bibliography.
- `article.pdf` — compiled 23-page article, with clickable references and contents.
- `build.sh` — PDF build script.
- `code/verify_identities.py` — exact finite symbolic checks.
- `requirements.txt` — the SymPy version used for verification.
- `data/verification.json` — every check and its result, with environment versions.
- `data/verification.txt` — readable run summary.
- `data/build_validation.json` — recorded PDF/build validation.
- `REPOSITORY_SCOPE.md` — repository audit scope and pinned source paths.

## Build the PDF

From this directory, with a standard TeX Live or MiKTeX installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `sh build.sh`. No bibliography processor, external figures,
network downloads, or shell escape are needed. Packages are listed in the source
preamble. Auxiliary TeX build files are intentionally omitted from this archive.

## Reproduce the checks

The recorded run used **Python 3.13.5** and **SymPy 1.14.0**.

```sh
python -m pip install -r requirements.txt
python code/verify_identities.py --output data/verification.json
```

The run passed **259/259** finite checks:

| Group | Passed / total |
|---|---:|
| Derivation identities | 41 / 41 |
| Primitive identities | 15 / 15 |
| Formal small-series identities | 24 / 24 |
| Coherent total-derivative examples | 8 / 8 |
| General resolvent residuals | 81 / 81 |
| Factorial-series residuals | 13 / 13 |
| Whole-prefix coefficient recurrences | 9 / 9 |
| Constant-coefficient operator examples | 33 / 33 |
| Matrix identities | 35 / 35 |

A matrix identity or a whole-prefix identity counts as one check. These checks
use exact symbolic arithmetic and finite truncations; they are not a formal
verification of infinite-support arguments, class foundations, or the general
nonexistence theorems. No numerical specialization is used as a surrogate for a
surreal proof.

## PDF validation

The final build has zero LaTeX errors, warnings, undefined references/citations,
and overfull or underfull boxes. All 23 pages were rendered with Poppler; the
layout was visually reviewed, with additional bounding-box checks finding no text
outside the stated safety margins. Rendering intermediates and font files are
not included.
