# Signed Condensation in Quadratic-Feedback Transseries

**Sharp reversion, universal cancellation, and inverse Borel growth**  
Research report prepared for Vladimir Reshetnikov, September 29, 2026.

## Main result

For the formal equation

    U(q) = sum_{j>=1} w_j q^j exp(lambda_j U(q)),

assume w_1=1, nonnegative primitive weights and slopes, and, outside a finite
prefix, w_j=1 and lambda_j=a*j^2+b*j+d with a>0. Put beta=lambda_1+w_2.
If Q is the compositional inverse, its coefficients satisfy

    [u^n] Q(u) ~ -S_n exp((b-beta)*r_n/a),
    r_n*(1+r_n)*exp(2*r_n) = a*n,
    S_n = exp(n*r_n*(1+2*r_n)/(1+r_n)) / sqrt(1+4*r_n+2*r_n^2).

The pure-model specialization proves the explicit quadratic inverse
conjecture in ProveIt's `Finite_Core_Universality_Exponential_Feedback`
article at the pinned snapshot. The manuscript also proves eventual
negativity, finite-prefix sensitivity, a positive-axis inverse Borel growth
equivalent, and a least-formal-term equivalent.

(Editorial, 2026-09-29: this is the third independent claimed proof of that
conjecture. The main theorem, with the same hypotheses, and all of the
further results except the least formal term are also in the earlier-filed
`../Quadratic_Exponential_Feedback_After_Reversion/` (batch 49), which this
article could not see; `../Signed_Quadratic_Feedback_Inversion/` (batch 49)
proves the pure-model law under different hypotheses. See "Editorial
amendments" below.)

The central argument estimates all configurations with at least two actions
above a sufficiently large fixed cutoff by an arbitrarily small polynomial
multiple of S_n, before cancellation. The remaining one-action contribution
is evaluated using a finite analytic inverse core.

## Contents

- `article.pdf`: compiled manuscript, including nine further research questions (20 pages as delivered; 22 pages after the editorial rebuild of 2026-09-29).
- `article.tex`: standalone LaTeX source (no ProveIt checkout or external TeX inputs required).
- `code/verify.py`: exact finite algebra checks and floating asymptotic diagnostics.
- `data/*_exact_egf.csv`: integer-normalized coefficients V_n = n! v_n.
- `data/asymptotic_diagnostics.csv`, `data/table.tex`: diagnostic table data.
- `data/verification.json`, `data/verification_run.txt`: recorded run and check counts.
- `PROOF_STATUS.md`: proof dependencies, limits, and review targets.
- `SOURCES.md`: pinned repository provenance and primary literature.
- `BUILD_STATUS.json`: compilation and PDF inspection summary of the delivered 20-page build (kept as delivered; it does not describe the editorial rebuild).

## Reproduce

Python 3.10 or later is needed for the code. The recorded run used Python
3.13.5 and mpmath 1.3.0 (see BUILD_STATUS.json for the actual environment).
All coefficient calculations use standard-library exact integer or rational
arithmetic; mpmath is used only for the decimal asymptotic comparisons.

```sh
python -m pip install -r requirements.txt
python code/verify.py --degree 320
make pdf
```

(Editorial, 2026-09-29: `code/verify.py` now defaults to `--degree 320`, the
degree of the recorded run (the delivered default was 240, which rewrote
`data/pure_a1_exact_egf.csv` shorter), and writes into `rerun/` beside
`code/` unless given `--output-dir`; writing into the recorded `data/`
requires `--overwrite-recorded`. `make verify` therefore also writes into
`rerun/`. On Windows use `py` instead of `python`, or
`uv run --no-project --with mpmath==1.3.0 python code/verify.py`.)

The supplied run passed 255 exact assertions in five models. Coefficients
were computed through degree 320 in the pure a=1 model and through degree
160 in each additional model. Numerical diagnostics are not interval
certificates and do not prove the asymptotic assertions.

`article.tex` embeds the recorded table. Re-running the script regenerates
`table.tex` in its output directory; changing the sample degree does not automatically replace
the embedded table or update the manuscript's reported check settings.

## Status

These are mathematical proofs submitted for independent review, not a
Lean-verified development. The novelty claim is limited to the audited
repository conjecture and the extensions proved in the report, not an
exhaustive claim of priority over all literature. A finite table is not
presented as proof. The least term is not an analytic remainder theorem.
No repository files were modified or uploaded.

## Editorial amendments (ProveIt, 2026-09-29)

Filed on 2026-09-29 (batch 50 of `docs/incoming/`; see `docs/incoming/README.md`).
The following changes were made; every change to the article source is
preceded by a `% ed. (2026-09-29)` comment, the visible additions are labelled
"Editorial note (ProveIt, 2026-09-29)", and no label was renamed.

- `article.tex`:
  - an unnumbered `ednote` environment (no numbering shifts), and no page
    anchors on the title page (removes a duplicate `page.1` destination
    present in the delivered build);
  - after the provenance paragraph: the cited lines 1623--1678 and 1661--1668
    are those of the pinned blob; after the editorial pass of 2026-09-29 they
    are 1666--1721 and 1704--1711 of
    `../Finite_Core_Universality_Exponential_Feedback/article.tex`, followed by
    an editorial note recording the claimed proofs;
  - after Corollary `cor:prefix`: this is a third independent claimed proof of
    `conj:quadratic-inverse`. `../Quadratic_Exponential_Feedback_After_Reversion/`
    (Theorem `thm:main`) has the same hypotheses, with `b, d, beta` written
    `d, e, mu`; its `cor:universality` is `cor:prefix` here and its
    `thm:borel` is `thm:borel` here. `../Signed_Quadratic_Feedback_Inversion/`
    (Theorem `thm:main`) has an exact tail `a j^2` and signed exceptions. The
    three sets of exact coefficients agree at every common degree (through
    240 for `a = 1`, 160 for `a = 2`); `thm:least` sharpens the second
    package's least-term index and adds the value; none of the proofs has been
    independently reviewed;
  - after the remark following `thm:least`: at `a = 1`, `b = d = 0` its
    constant `1/4` is that of the negative-ray article's remainder bound
    (`../Negative_Ray_Summation_Exponential_Feedback/`, `thm:optimal`); the
    least term is formal and gives no lower bound for the truncation error;
  - research questions 1 (answered: signed-inversion `thm:two`,
    quadratic-inverse `thm:sharp`, `cor:minimalcore`), 4 (answered:
    quadratic-inverse `thm:borderline`, factor `e^(kappa/(2a))`), 6 (partly:
    signed-inversion `thm:borel`, maximum modulus on circles; natural
    boundaries `../Natural_Boundaries_Quadratic_Exponential_Feedback/`
    `thm:main`(iii), no exponential bound in any sector about direction pi at
    `a = 1`) and 9 (partly: signed-inversion `thm:main`, signed finite
    exceptions): an editorial note after each;
  - bibliography entries `ed:qfr`, `ed:sqi`, `ed:nbq`, `ed:nrs`.
- `article.pdf`: rebuilt with three pdfLaTeX passes (22 pages, was 20; no
  errors, undefined references, multiply defined labels, duplicate
  destinations, overfull or underfull boxes; every font Type 1).
- `code/verify.py`: default `--degree 320`; outputs to `rerun/` unless
  `--output-dir` is given, with `--overwrite-recorded` required for `data/`;
  CSV rows, `table.tex`, `verification.json` and standard output are written
  with LF on every platform. A rerun on a copy (`--degree 320`) reproduced the
  five `*_exact_egf.csv`, `asymptotic_diagnostics.csv` and `table.tex` byte
  for byte, and `verification.json` and the captured standard output
  (`data/verification_run.txt`) except `elapsed_seconds`; the recorded `data/`
  is unchanged.
- `SOURCES.md` is kept as delivered. Its audited ranges of the finite-core
  article (lines 100--385, 490--785, 1530--1740 and 1660--1678 of the pinned
  blob) are lines 102--414, 519--814, 1573--1835 and 1703--1721 after the
  editorial pass of 2026-09-29; the conjecture environment (pinned 1661--1668)
  is at 1704--1711.
- `BUILD_STATUS.json` and `PROOF_STATUS.md` are kept as delivered; they
  describe the delivered build and the delivered article.
- `README.md`: this section and the notes in "Main result", "Contents" and
  "Reproduce".

On filing, the six CSV tables under `data/` were normalized from CRLF to LF;
every other file was filed byte for byte as delivered.
