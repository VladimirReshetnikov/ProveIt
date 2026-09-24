# A proof of the formulas in OEIS A260306

This archive contains a self-contained proof of both finite formulas in
OEIS A260306, for every nonnegative coefficient index. The main article
includes the analytic error estimate needed to identify the asymptotic
coefficients, rather than only showing that the two sums agree.

## Main result

For Ramanujan's function defined at positive integers N by

    sum(k=0..N-1, N^k/k!) + theta(N)*N^N/N! = exp(N)/2,

write theta(N) ~ sum(n>=0, c_n/N^n). Then

    c_n = -2^n n! [z^(2n+1)] (z^2 / (2*(exp(z)-1-z)))^(n+1).

The article derives the OEIS double and triple sums exactly from this
identity. For each fixed R >= 1 it also proves

    theta(N) = sum(n=0..R-1, c_n/N^n) + O_R(N^(-R)).

The numerator of c_n in lowest terms is A260306(n), and its positive
denominator is A065973(n).

## Files

- `a260306_proof.pdf`: the complete typeset article.
- `a260306_proof.tex`: its editable, self-contained LaTeX source.
- `code/verify.py`: exact rational computations by five representations:
  the inverse-function recurrence, inverse-power coefficient extraction,
  the OEIS double sum, the literal triple sum, and the associated
  Stirling-number sum.
- `code/numerical_check.py`: optional high-precision asymptotic examples.
- `artifacts/coefficients.csv`: 118 independently generated rational
  coefficients, indexed 0 through 117, as reduced numerators and denominators.
- `artifacts/reference_prefix.json`: the externally sourced reference
  prefixes, source URLs, and access date.
- `artifacts/checks.json` and `artifacts/verification_log.txt`: the
  executed exact-check results and their precise ranges.
- `artifacts/numerical_checks.csv`, `artifacts/numerical_summary.json`,
  and `artifacts/numerical_log.txt`: numerical results and execution details.
- `requirements-optional.txt`: the numerical dependency used in this run.
- `Makefile`: convenient build and check targets.

The CSV files are plain text. Some spreadsheet applications round long
integers on import; use a text editor, Python integers, or import the
numerator and denominator columns explicitly as text.

## Reproduce the exact checks

From the archive's root directory:

    python3 code/verify.py

Python 3.10 or later is sufficient. No third-party package and no network
connection are required. The executed default run:

* generated c_0 through c_117;
* compared the recurrence, inverse-power algorithm, double sum, and
  associated Stirling-number sum for n = 0,...,20;
* compared the literal triple sum for n = 0,...,10;
* compared 17 numerator values and 14 denominator values with the prefixes
  retrieved from OEIS.

All of these checks passed. They supplement the all-index mathematical
proof. The generated 118-term table was NOT compared in its entirety
against an externally downloaded OEIS b-file in this run.

Custom bounds and output directory can be supplied, for example:

    python3 code/verify.py --max-n 30 --formula-max 30 --triple-max 12 \
        --out-dir custom_results

The optional command

    python3 code/verify.py --check-oeis

also fetches both public OEIS b-files and checks every generated index.
It requires ordinary outbound network access. The container used to
prepare this archive could not resolve the external host, so that optional
live comparison was not completed. The offline reference fixture was
instead populated from the entries successfully retrieved in the browser.

## Reproduce the numerical illustration

    python3 -m pip install -r requirements-optional.txt
    python3 code/numerical_check.py

The included results used Python 3.13.5 and mpmath 1.3.0 with 100 decimal
digits of working precision. The function is evaluated both from its
scaled finite-sum definition and from a regularized incomplete gamma
function. Their maximum absolute discrepancy over the tested arguments
was approximately 7.176e-99. These are high-precision consistency checks,
not rigorous interval certificates. The article independently proves the
asymptotic remainder estimate.

## Build the PDF

With a LaTeX distribution containing the standard packages used in the
preamble (including newtx and latexmk):

    latexmk -pdf -interaction=nonstopmode -halt-on-error a260306_proof.tex

Or use `make pdf`. Bibliographic entries are embedded in the source; no
BibTeX run, external figure, or copied source article is required.
`make check` runs the exact checks, and `make numerical` runs the optional
numerical script after its dependency is installed.

## Sources and scope

The source entries were consulted on September 20, 2026:

    https://oeis.org/search?q=id:A260306&fmt=text
    https://oeis.org/A065973

For related coefficient formulas and the larger context, the article
cites Cormac O'Sullivan, *Ramanujan's approximation to the exponential
function and generalizations*, arXiv:2205.08504 (2022):

    https://arxiv.org/abs/2205.08504

No claim of novelty for Ramanujan's expansion or the general coefficient
theory is made. The specific accomplishment here is the complete proof
of the two formulas asked about, including their exact normalization.
