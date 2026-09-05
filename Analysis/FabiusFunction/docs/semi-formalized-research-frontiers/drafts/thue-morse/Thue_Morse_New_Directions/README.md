# Thue–Morse Beyond the Atlas

**Boundary Defects, Nonlinear Prouhet Geometry, and Flat Automatic q-Products**  
Research draft dated 4 September 2026.

## Read the article

`thue_morse_new_directions.pdf` is the compiled article.
`thue_morse_new_directions.tex` is its standalone LaTeX source. The bibliography
is embedded in the source; no external BibTeX database or repository macros
are required. The included `saddle_errors.pdf` is the sole external figure.

The article develops three directions:

1. An explicit finite boundary functional for every-order Thue–Morse correlations,
   including exact odd-order telescoping and arbitrary block-multiple formulas.
2. Hypergraph-cover formulas for nonlinear Prouhet sums, quadratic hafnian
   coefficients, explicit path examples, and a matching-polynomial crossover.
3. A Thue–Morse-weighted geometric product, its smooth flatness, an all-order
   Lambert-W saddle expansion, and a joint endpoint profile that includes
   Phi_q(q) = 1/sqrt(2) + O((-log q)^M) for every fixed M as q approaches 1.

Classical ingredients are credited. Historical priority is not certified;
see `SOURCE_AUDIT.md`. No Lean formalization or peer review is claimed.

## Compile

With a standard TeX distribution containing the packages named in the source:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error thue_morse_new_directions.tex
```

Alternatively, run `pdflatex thue_morse_new_directions.tex` three times.
`build.sh` performs the latexmk build, with a three-pass pdflatex fallback.

## Reproduce the checks

Python 3.10 or later is required. The combinatorial tests use exact integers,
fractions, and symbolic expressions; the analytic tests use multiprecision
floating-point arithmetic.

```sh
python -m pip install -r requirements.txt
python verify.py --plots
```

Without `--plots`, matplotlib is not needed. The program writes the CSV and
JSON files beside the script. Runtime depends on the machine and precision;
the positive series for the smallest t is the largest numerical calculation.

The supplied run passed:

- 1,800 even-order correlation assertions;
- 960 additional odd-order and block-multiple correlation assertions;
- 35 hypergraph moment equalities, 9 path examples, and 6 matching-polynomial checks.

The numerical saddle tests used 80 decimal digits. Bounds reported for omitted
positive-series tails do NOT certify all numerical roundoff or product errors.
This is not an interval-arithmetic proof. A printed zero numerical residual
means agreement at working precision, not an exact symbolic identity.

## Files

- `verify.py`: commented implementation and reproducible checks.
- `verification_results.json`: machine-readable results of the supplied run.
- `verification_run.txt`: captured verification output.
- `correlations.csv`: finite correlation examples.
- `path_moments.csv`: first nonzero moments in the path family.
- `saddle.csv`: leading and first-corrected saddle errors and tail bounds.
- `boundary_layer.csv`: diagonal convergence to 1/sqrt(2).
- `saddle_errors.pdf`: vector figure used in the article.
- `SOURCE_AUDIT.md`: sources, novelty boundaries, and review scope.
- `environment.json`: versions actually present for this run.
- `SHA256SUMS.txt`: hashes of the distribution files, excluding this hash file.

The archive does not contain copies of the cited authors' papers, repository
sources, font files, or temporary LaTeX build outputs.
