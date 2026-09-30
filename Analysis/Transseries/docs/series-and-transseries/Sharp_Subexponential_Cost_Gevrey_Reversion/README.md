# Sharp Subexponential Reversion

**Exact extremal cost, a Gevrey transition, and composition of two divergent series**

Prepared for Vladimir Reshetnikov, 29 September 2026.

The package contains a 22-page research article, its LaTeX source, exact finite
verification code, and explicitly non-certified numerical diagnostics.

## Research target

This continues the research questions “Optimal subexponential cost of reversion”
and “Two divergent composition arguments” in ProveIt's
`Sharp_Weighted_Type_Formal_Reversion/article.tex`, at repository snapshot
`5c695cfdf70a8b6c91bd5b2c1e99e3baecd5a864`.

Exact type preservation was already established in that repository. It is not
claimed as a new result here. The new contribution relative to those stated
questions is the sharp fixed-ball analysis, the factorial-weight two-divergent
composition law, and the explicit limitation on full inverse root limits.
No worldwide priority claim or Lean verification is asserted.

## Main results

For the coefficient ball

    f(z) = z + sum_{n >= 2} a_n z^n,
    |a_n| <= C A^(n-1) ((n-1)!)^s,

one series, with all nonlinear coefficients negative and saturating the bounds,
simultaneously maximizes every inverse coefficient in absolute value. Let R_n
be that coefficient divided by C A^(n-1) ((n-1)!)^s. The article proves:

* log R_n ~ C n^(1-s) for 0 < s < 1;
* R_n ~ exp(C n^(1-s)) for s > 1/2, locally uniformly in s and C;
* R_n ~ exp(C sqrt(n) + 3 C^2/4 + sqrt(2) C) at s = 1/2;
* R_n -> exp(C exp(-t)) when s = 1 + t/log(n), uniformly on bounded t-sets.

It also treats the unshifted factorial ball |a_n| <= B A^(n-1) (n!)^s;
its constants differ and are stated explicitly in Corollary 2.3.

For s-type tau_s(f) = limsup (|f_n|/(n!)^s)^(1/n), and invertible linear parts,

    tau_s(f o g) <= max(tau_s(g), |g_1| tau_s(f)),

with equality when the two quantities on the right are unequal. Equal-type
cancellation is unavoidable. A separate counterexample has strictly positive
forward coefficients and a full normalized root limit, but infinitely many
zero coefficients in its inverse.

## Boundaries

For 0 < s < 1/2 the optimal leading logarithmic cost is proved, not a complete
multiplicative equivalent. The composition theorem is for factorial powers,
not all superexponential weights. No feedback-specific inverse equivalent,
Borel summability theorem, or analytic realization theorem is claimed.

## Build the article

Run from this directory, retaining the supplied `data/*_table.tex` files:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

The bibliography is embedded. No BibTeX or network access is required. Standard
TeX Live packages used include Latin Modern, amsmath, amsthm, microtype,
booktabs, hyperref, and cleveref.

## Reproduce the checks

Exact tests use Python's standard library:

    python code/verify.py --order 45

Optional diagnostics require NumPy and mpmath:

    python code/verify.py --order 45 --diagnostics --mp-check

The recorded run tallies 5,338 scalar equalities/inequalities, including all 512
sign patterns in a degree-ten factorial coefficient box. Internal exact
divisibility assertions provide additional checks. Both composition directions
are checked independently. These are finite tests, not proofs of asymptotic
statements and not Lean verification.

The diagnostic routine requires extended-range NumPy `longdouble` and raises a
clear error when the platform provides only ordinary double range. It uses
positive terms and checks finiteness. Three degree-80 cases are independently
recomputed with mpmath at 80 decimal digits. None is an interval certificate.
The article does not infer an onset or a convergence rate from the diagnostics.

The default output is `data/rerun`, so a rerun does not overwrite recorded data.
To regenerate the printed tables from a diagnostic run:

    python code/render_tables.py --input data/rerun --output data

The supplied tables were generated from `data/recorded`.

## Files

* `article.tex`, `article.pdf`: article source and compiled PDF.
* `code/verify.py`: exact finite tests and optional numerical diagnostics.
* `code/render_tables.py`: deterministic CSV-to-LaTeX table rendering.
* `data/recorded/`: original check ledger and numerical CSVs.
* `data/*_table.tex`: supplied article tables.
* `data/build_validation.json`: compile, geometry, font, and visual checks.
* `provenance.json`: snapshot, source paths, and scope.

No repository or persistent Library file is modified by this package.
