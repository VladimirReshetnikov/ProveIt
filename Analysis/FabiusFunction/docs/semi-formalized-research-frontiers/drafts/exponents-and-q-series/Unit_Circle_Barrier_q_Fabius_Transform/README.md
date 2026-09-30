# The Unit-Circle Barrier for the q-Fabius Transform

**Natural boundaries, cyclotomic moment poles, and exterior meromorphic divisors**

Research article prepared for Vladimir Reshetnikov, September 30, 2026.
The PDF contains 22 pages, including complete proofs, a bibliography, a repository
interface audit, computational examples, and further research questions.

## Main result

For every fixed nonzero complex z, the function

    A(q,z) = product_{j>=0} h((1-q) q^j z),     |q| < 1,
    h(w) = (exp(w)-1)/w,                      h(0) = 1,

has the whole unit circle as a natural boundary, even for meromorphic
continuation. The proof combines a nonvanishing root-of-unity cusp coefficient
with a quantitative construction of zeros approaching the boundary.

Other proved results include stability under positive finite products with real
dilations, all-orders radial cusp expansions, exact leading cyclotomic poles of
moment coefficients, a sharper denominator bound, and a complete formula for the
exterior transform's poles and their multiplicities. The functions are not
algebraic or D-finite in q for fixed z != 0.

## Files

- `q_fabius_boundary.pdf`: the article.
- `q_fabius_boundary.tex`: self-contained LaTeX source with embedded bibliography.
- `verify_results.py`: independent exact and high-precision checks.
- `verification_results.json`: full verification receipt, including numerical data.
- `verification_run.txt`: execution transcript.
- `requirements.txt`: versions used for verification.
- `build.sh`: PDF build helper for a Unix-like shell.
- `SHA256SUMS`: hashes of the package files other than the hash manifest itself.

## Rebuild the article

Requires a TeX Live installation providing the packages named in the source
preamble, including newtx, amsmath, amsthm, mathtools, geometry, microtype,
hyperref, xurl, fancyhdr, enumitem, and booktabs. No external figures, BibTeX run,
network access, or font files from this package are required.

    pdflatex -interaction=nonstopmode -halt-on-error q_fabius_boundary.tex
    pdflatex -interaction=nonstopmode -halt-on-error q_fabius_boundary.tex

Or run `bash build.sh` in this directory. Rebuilding creates ordinary TeX
auxiliary files alongside the source.

## Run the checks

Use Python 3.10 or newer; the recorded run used Python 3.13.5, SymPy 1.14.0,
and mpmath 1.3.0.

    python -m pip install -r requirements.txt
    python verify_results.py

The successful run checks:

- agreement of two moment recurrences and the q=0 and q=1 specializations
  through degree 12;
- 46 exact cyclotomic leading-coefficient identities;
- 11 cyclotomic denominator tests, including observed minimality through degree 12;
- 1,800 exact exterior-pole collision counts;
- radial cusp examples at six root orders and zero-condensation examples, using
  85-decimal-digit working precision.

Exact checks use rational arithmetic and cyclotomic quotient rings. Numerical
checks are not interval-arithmetic certificates. The script overwrites the JSON
receipt when it runs. Its finite checks supplement, and do not replace, the proofs.

## Research status and limitations

The main natural-boundary and exterior-divisor results are proved in the article.
The conjecture that the displayed upper denominator is minimal in *every* degree
is not proved; finite computations verify it only through degree 12. Neither
nonlinear differential transcendence nor convergence/Borel summability of the
full cusp correction series is asserted.

No Lean file was compiled for this package. These are conventional mathematical
proofs, not machine-certified Lean results. Worldwide publication priority has
not been independently established. The article distinguishes established
q-product methods from its specific arguments and conclusions.

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 7747fcfddedeca1a04b6526cdd4836fbfdad1b89
Inspected interface document: Analysis/FabiusFunction/README.md
README blob: 8a19a7c8de8939c4a55ec63fc443ce08d6fe74ce

The audit covers the documented geometric-uniform interfaces relevant to the
article, not every document, incoming archive, or proof in the repository. No
repository files were changed. External mathematical references are given in
the article's bibliography.

## Artifact validation

The delivered PDF compiled without unresolved references, TeX errors, or
underfull/overfull box warnings. All 22 pages were rendered for visual review;
selected formula, table, contents, and audit pages were also inspected at full
page resolution. SHA256SUMS permits checking the delivered file bytes.
