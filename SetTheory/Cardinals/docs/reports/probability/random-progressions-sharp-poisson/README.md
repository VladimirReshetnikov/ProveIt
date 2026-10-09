# Sharp Poisson asymptotics for random arithmetic progressions

**Research manuscript, October 7, 2026.** Prepared by ChatGPT (OpenAI) for
Vladimir Reshetnikov's ProveIt research program.

The PDF contains complete written arguments for the stated results. It is
unrefereed, is not Lean-verified, and has no certified claim of literature
priority. The executable checks are finite regressions, not a proof of the
asymptotic statements.

## Main results

For a Bernoulli-p subset of [n], with p fixed in (0,1), let U_n be the longest
nonconstant arithmetic progression. Let M_r(n) count r-term progressions,
and set

```text
lambda(n,r) = M_r(n) p^r - M_(r+1)(n) p^(r+1)
c_p = ((1-p)/p) (5/3 - pi^2/9).
```

Theorem 1.1 proves the uniform corrected approximation

```text
P(U_n < r) = exp(-lambda) (1 + c_p lambda^2 r^2/n)
             + O_p((log n)^(3/2)/n),  2 <= r <= n.
```

Theorem 1.2 gives its logarithmic critical-window version with an
O(r^(3/2)/n) remainder. Theorem 1.3 identifies a lattice-periodic leading
coefficient for the uncorrected uniform error, proves that its order is
exactly Theta_p((log n)^2/n), and computes its normalized liminf and limsup.
All three results also hold for the smooth Zhao--Zhang Poisson parameter.
A separate proposition treats fixed progression length and sparse density.

The manuscript compares the new sharp statements to the explicit
O(n^-1 log^4(n) log log(n)) estimate in the inspected Zhao--Zhang preprint.
It credits the existing progression-head construction, pair-overlap bounds,
and general cumulant methodology. It does **not** claim an improvement to a
deterministic Szemeredi or van der Waerden bound.

## Contents

- `paper.pdf`, `paper.tex`, `references.bib`: article and complete source.
- `code/verify.py`: exact event, mean, covariance, and overlap regressions.
- `code/approximation.py`: numerical evaluation of the asymptotic formulas.
- `code/check_lattice.py`: numerical checks of the lattice maximization.
- `results/`: recorded checks, incidence-degree data, and formula diagnostics.
- `notes/`: novelty/provenance note, audit, and formalization roadmap.
- `claims.json`: machine-readable claim/dependency/status ledger.
- `INTEGRATION.md`, `build.sh`, `Makefile`: build and repository integration.
- `SHA256SUMS`: integrity hashes of the bundled files, excluding itself.

## Reproduce

Python 3.10+ and its standard library are sufficient for every check.

```sh
python3 code/verify.py
python3 code/check_lattice.py
python3 code/approximation.py 1000000 33 --p 0.5
```

The full recorded run passed 114,176 configuration/threshold instances,
21,183 one-site covariance identities, 9,546 multiply-overlapping pair
classifications, and 810,589 triple configurations. The parameter counts
and details are in `results/verification.json`. Eight logarithmic sandwich
checks and the lattice diagnostics use floating point and are labeled as
such. No Monte Carlo is used.

The calculator produces an asymptotic estimate, **not a certified finite-n
confidence interval**. The theorem's implicit constants and effective
starting n are not numerically optimized. Lattice diagnostics compare
formula coefficients; they do not measure the true avoidance probabilities
at huge n.

A conventional TeX installation with pdfLaTeX and BibTeX is sufficient:

```sh
./build.sh
# alternatively
make paper
```

The build script also accepts `bibtex8` or `bibtex.original` when `bibtex` is
not available. Common required packages are listed in the TeX preamble.

## Suggested integration

The ZIP is laid out under

```text
Combinatorics/Ramsey/Research/RandomProgressions/SharpPoisson/
```

No GitHub changes have been made. Review `INTEGRATION.md` before merging the
research into any trusted proof or formalization index.
