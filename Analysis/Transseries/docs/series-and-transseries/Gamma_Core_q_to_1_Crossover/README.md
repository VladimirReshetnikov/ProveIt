# A Gamma Core Across the q → 1 Crossover

**Uniform exponential accuracy, inverse stability, and arithmetic convergence**

Research manuscript prepared for Vladimir Reshetnikov, September 29, 2026.
The PDF contains 30 pages, including the title page and two-page contents
(31 pages since the editorial rebuild of 2026-09-29; see the last section).

## Files

- `Gamma_Core_Transseries.pdf`: complete article, proofs, numerical tables,
  repository provenance, bibliography, and ten further research directions.
- `Gamma_Core_Transseries.tex`: self-contained LaTeX source with an embedded
  bibliography; no external figures or custom font files are required.
- `code/verify.py`: exact rational coefficient audits and high-precision
  checks of the central Gamma-core approximation, inverse, and flat defect.
- `code/verify_supplement.py`: checks of the multinomial extension, relative
  derivative estimate, endpoint curvature, and other half-integer sheets.
- `data/verification_quick.json`: recorded successful 100-digit main suite.
- `data/verification_supplement.json`: recorded successful supplemental suite.
- `SOURCE_MANIFEST.json`: pinned repository source and result-scope metadata.
- `AUDIT.md`: mathematical and artifact verification record.
- `requirements.txt` and `build.sh`: reproducibility helpers.

## Research target and results

The inspected ProveIt companion explicitly leaves uniform matching of its
q-to-1 crossover expansion down to tau = 0 for a different error analysis.
The article resolves that question for the canonical central Gaussian-binomial
interpolation. It keeps the classical Gamma quotient exact, regularizes the
remaining coefficient functions, and proves an exact real-index
Euler–Maclaurin remainder identity.

For h = log(q) tending to zero, truncation at
K = max(2, ceil(2*pi^2/h)) has global logarithmic error at most
(8 + o(1))*exp(-4*pi^2/h), uniformly for all real indices x >= 0.
An exact modular limit supplies a matching exponential lower bound for this
uncorrected truncation family. A derivative-sensitive argument gives a global
inverse error at most (24*pi^2 + o(1))*exp(-4*pi^2/h), including the quadratic
zero-slope endpoint. A balanced Gaussian-multinomial extension has a uniform
value-error bound independent of the positive weights.

Separately, the fixed-index algebraic series has positive convergence radius
exactly when 2*x is an integer. At nonintegral half-integers, its convergent
analytic sum still misses the exact flat term 4*M(h) - 2*M(h/2), where M is a
modular Euler-product logarithm. The same defect occurs on every nonintegral
half-integer sheet.

## Scope and status

The manuscript contains mathematical proofs, not only experiments or proposed
proof outlines. It is not independently refereed and is not Lean-verified.
Classical q-asymptotic, Euler–Maclaurin, Gamma, Mellin, Bernoulli, and modular
methods are explicitly credited. Historical priority over the complete
q-asymptotics literature has not been established.

The result concerns a specified canonical real interpolation. It does not
claim uniqueness from integer values alone, a full complex-sector resurgence
or Stokes theorem, a sharp inverse-error lower bound, or a general multinomial
inverse theorem. Those distinctions and further questions are in the article.

The numerical checks use high-precision floating-point arithmetic, NOT
outward-rounded interval arithmetic. Analytic error inequalities are proved
in the article, but the computed decimal evaluations are not interval
certificates. The exact rational coefficient checks use SymPy.

## Build the PDF

A standard TeX Live or MiKTeX installation with pdfLaTeX and the packages
listed in the source is sufficient. From this directory run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Gamma_Core_Transseries.tex
pdflatex -interaction=nonstopmode -halt-on-error Gamma_Core_Transseries.tex
pdflatex -interaction=nonstopmode -halt-on-error Gamma_Core_Transseries.tex
```

On a Unix-like shell, `sh build.sh` performs these passes. The third pass
stabilizes page references after the table of contents is generated.

## Reproduce the recorded computations

Python 3.10 or later is recommended. The recorded runs used Python 3.13.5,
mpmath 1.3.0, and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python code/verify.py --quick
python code/verify_supplement.py
```

The first command runs the recorded 100-digit parameter grid. It includes
42 exact Faulhaber comparisons, three finite-product comparisons, six forward
checks, two inverse checks, two half-integer checks, and five recorded
large-order ratios. The supplementary script has eight additional numerical
identity or bound checks. Both scripts write JSON into `data/`.

Running `verify.py` without `--quick` requests a larger exploratory grid at
190 digits. That larger grid is NOT the source of the article's tables and
is not represented as a completed recorded run in this package. The main
and supplemental suites are enough to reproduce all numerical values cited
in the article.

## Pinned source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Snapshot: `aa06d3e29498aaa37a5b7924764d8a7b6f9d9ce0`

Relevant companion:
`Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`

The endpoint qualification appears after `t3:eq:Ssmall` and `t3:eq:Slarge`,
around source lines 4195–4210. Full provenance and source labels appear in
Appendix A and `SOURCE_MANIFEST.json`.

## Editorial amendments (ProveIt, 2026-09-29)

Changes made after filing (batch 46 of `docs/incoming/README.md`), file by
file. Every change to the article source is marked with a
`% ed. (2026-09-29)` comment; visible additions are labelled "Editorial
note (ProveIt, 2026-09-29)" or "[Editorial addition, ProveIt, 2026-09-29.]".

- `Gamma_Core_Transseries.tex`:
  - an editorial note at the end of Section 1 naming the four sibling
    packages of the same `q → 1` merge unit
    (`../Uniform_q_Multinomial_Certified_Inversion/`,
    `../Uniform_Resurgent_Crossover_Gaussian_Binomials/`,
    `../Certified_Inversion_q_to_1_Transition/`,
    `../Theta_Resolved_Optimal_Truncation_q_Multinomial/`) and saying that
    this article is complementary to them (Gamma quotient kept exact,
    expansion in `h`, action `4π²` of the modular term, against their
    `e^{−2π a_* x}` least remainders); relating Theorem
    `q3:thm:double-scaling` of
    `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/combinatorial-coefficient-calculus/Gaussian_Coefficient_Calculus/`
    (same `τ ≥ τ₀` restriction; its central case, with its `τ` equal to
    `2hx`; a term-by-term comparison is left to the merge); and naming the
    canonical volume's `p0:thm:optimal-truncation` and the Lean theorems
    `Fabius.exists_eq_in_residual_interval` and `Fabius.transport_bound`
    (related, not relied on: they assume the positive derivative bound that
    Theorem 7.3's endpoint argument avoids); the article cites none of them;
  - Appendix A: "at the pinned tree" corrected to "at the pinned commit"
    (the pin is a commit);
  - `\hypersetup{pageanchor=false}` around the title page, which removes a
    duplicate `page.1` hyperlink destination;
  - four editorial bibliography entries (`ed:siblings`, `ed:gcc`, `ed:tai`,
    `ed:lean`).
- `Gamma_Core_Transseries.pdf`: rebuilt with `build.sh` (three pdfLaTeX
  passes); 31 pages; no errors, undefined references, overfull boxes or
  duplicate destinations (one underfull bibliography line, as delivered).
  `SOURCE_MANIFEST.json` (`pdf_pages: 30`) and `AUDIT.md` ("All 30 pages")
  describe the delivered PDF and are kept unchanged as its record.
- `code/verify.py`, `code/verify_supplement.py`: JSON written with
  `newline='\n'` (LF on Windows too). Reruns on a copy (Python 3.13.5,
  `mpmath==1.3.0`, `sympy==1.14.0`) of `code/verify.py --quick` and
  `code/verify_supplement.py` reproduced `data/verification_quick.json` and
  `data/verification_supplement.json` byte for byte.
- `README.md`: the page-count note and this section.
