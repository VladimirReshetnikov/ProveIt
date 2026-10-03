# Natural Boundaries Survive Nonlinear Feedback

**Moving-parameter partial theta series, sharp half-plane realization, and the failure of angular Borel summation**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

`natural_boundaries_feedback.pdf` is the compiled A4 article (21 pages as delivered; 22 pages after the editorial rebuild of 2026-09-29).
`natural_boundaries_feedback.tex` is its standalone editable source, including the bibliography.

## Principal contribution

For every integer d >= 2, consider

    U_d(q) = sum_{j>=1} q^j exp(j^d U_d(q)).

The canonical actual inverse Q_d is holomorphic in a small left half-disc and smooth to its imaginary diameter. The article proves that **every point of that diameter is a natural boundary point**. Its locally univalent image is a curved natural boundary for the forward function U_d.

For d = 2, this supplies a negative answer to the angular-continuation question left open in ProveIt's `Negative_Ray_Summation_Exponential_Feedback` article. (Editorial, 2026-09-29: for d = 2 that answer was already given, independently, by the earlier-filed `../Natural_Boundaries_Quadratic_Exponential_Feedback/` (batch 49), which this article could not see; the cases d >= 3 are new to the repository and answer that package's higher-degree question for integer d. See "Editorial amendments" below.) Both formal series have entire integrated Borel transforms and admit fine negative-ray summation, yet neither admits angular 1-summation in any open interval containing the negative direction.

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
mkdir -p rerun
python code/verify.py --order 24 > rerun/run_output.txt
```

(Editorial, 2026-09-29: the delivered recipe redirected into
`data/run_output.txt`, and the program always rewrote `data/`. It now writes
into `rerun/` beside `code/` unless given `--output-dir`, and writing into the
recorded `data/` requires `--overwrite-recorded`. On Windows use `py` instead
of `python`, or `uv run --no-project --with mpmath==1.3.0 python
code/verify.py --order 24`.)

The recorded full run used Python 3.13.5 and mpmath 1.3.0. It passed 324 exact finite comparisons, ten moving-curve asymptotic diagnostics, four rational-boundary root calculations, 352 quadratic Fourier checks, and a tied-pole mean-square check. Numerical diagnostics used 110-digit working precision, not interval arithmetic.

Running the program replaces the data files in its output directory (since the editorial amendments, `rerun/` by default, not the recorded `data/`). An exact-only run marks numerical diagnostics as not run. The full run restores their recorded status. A small numerical residual must not be interpreted as a certified decimal enclosure.

## Package contents

- Article source and PDF.
- `code/verify.py`: independent formal, inverse, kernel, and tree-block constructions.
- `data/coefficients.csv`, `data/blocks.json`: exact finite output.
- `data/moving_curve_ratios.csv`, `data/boundary_points.csv`: floating-point diagnostics.
- `data/verification.json`, `data/run_output.txt`: actual execution records. The two files are identical: `run_output.txt` is the redirected standard output of `code/verify.py`, which prints the JSON it writes.
- `notes/proof_status.md`: proof dependencies, boundaries, and audit.
- `notes/provenance.json`: repository snapshot, reviewed sources, and primary literature.
- `notes/build_validation.json`: PDF build and visual-inspection record of the delivered 21-page build (kept as delivered; it does not describe the editorial rebuild).

Repository snapshot: `ebd8344bca77d8352cd745b7df374618a290a029`. No upstream files were changed.

## Editorial amendments (ProveIt, 2026-09-29)

Filed on 2026-09-29 (batch 50 of `docs/incoming/`; see `docs/incoming/README.md`).
The following changes were made; every change to the article source is
preceded by a `% ed. (2026-09-29)` comment, the visible additions are labelled
"Editorial note (ProveIt, 2026-09-29)", and no label was renamed.

- `natural_boundaries_feedback.tex`:
  - an unnumbered `ednote` environment (no numbering shifts), and no page
    anchors on the title page (removes a duplicate `page.1` destination
    present in the delivered build);
  - after `thm:quadratic-main`: the case d = 2 of `thm:main` and
    `thm:quadratic-main` was proved independently in
    `../Natural_Boundaries_Quadratic_Exponential_Feedback/` (its `thm:main`),
    filed earlier and not visible from this article's snapshot, with the
    explicit radius 1/32, `|Q' - 1| < 1/3` and the nowhere-real-analytic image
    arc; its `thm:rigidity` is the case d = 2 of `thm:moving`, its
    `thm:rational-main` extends the d = 2 conclusions to rational amplitudes;
    the d = 2 coefficients agree with its recorded ones (through degree 16);
    the cases d >= 3 answer its question "Higher-degree and nonpolynomial
    slopes" for integer d;
  - the priority phrasing (abstract, a `% ed.` comment only; Section 1.1 and
    Section 1.3, a short editorial note each) points to that note;
  - research question "The angular growth of the entire Borel transform":
    for d = 2 the maximum modulus on circles is Theorem `thm:borel` of
    `../Signed_Quadratic_Feedback_Inversion/`; individual rays stay open;
  - research question "Actual optimal errors rather than positive majorants":
    for d = 2 the least formal term is Theorem `thm:least` of
    `../Signed_Condensation_Sharp_Quadratic_Reversion/` (batch 50), with the
    constant 1/4 of `eq:optimized`; formal only, the question stays open;
  - bibliography entries `ed:nbq`, `ed:sqi`, `ed:scs`.
- `natural_boundaries_feedback.pdf`: rebuilt with three pdfLaTeX passes (22
  pages, was 21; no errors, undefined references, multiply defined labels,
  duplicate destinations, overfull or underfull boxes; every font Type 1).
- `code/verify.py`: outputs go to `rerun/` unless `--output-dir` is given, and
  `--overwrite-recorded` is required for `data/`; CSV rows, JSON files and
  standard output are written with LF on every platform. A rerun on a copy
  (`--order 24`) reproduced all five files of `data/` and the redirected
  standard output (`data/run_output.txt`) byte for byte; the recorded `data/`
  is unchanged.
- `notes/proof_status.md`: an editorial note after the paragraph on proposed
  additions (d = 2 is in the earlier-filed package).
- `notes/build_validation.json` and `notes/provenance.json` are kept as
  delivered.
- `README.md`: this section and the notes in "Read", "Principal
  contribution", "Reproduce the checks" and "Package contents".

On filing, the three CSV tables under `data/` were normalized from CRLF to LF;
every other file was filed byte for byte as delivered.
