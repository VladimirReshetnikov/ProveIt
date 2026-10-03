# Support-Controlled Reversion and the Exact One-Exponential Substitution Group

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Start here

Read `reversion_and_one_exponential.pdf` (25 A4 pages with the editorial
notes of 2026-09-29; 23 as delivered). Its self-contained
editable source is `reversion_and_one_exponential.tex`; no files from the
ProveIt repository are needed to compile it.

The article addresses three specifically labeled questions in the ProveIt
transseries volume:

| Repository label | Article result |
| --- | --- |
| `plt:rmk:ext-open-burmann` | Theorem 3.2: integer-indexed Hahn Lagrange inversion, with a finite outer index bound at every power exponent. |
| `plt:rmk:ext-open-denominators` | Theorem 4.1 and Corollary 4.2: Newton iterates preserve the normalized support monoid; the optimal universal Puiseux denominator is the original denominator. |
| `plt:rmk:ext-open-resurgence` | Theorem 6.1, Corollary 6.4, and Section 7: obstruction to unrestricted one-exponential closure, maximal admissible sublinear substitution group, and exact-core inversion. This settles a formal algebraic component, not general resurgence. |

Theorem 8.1 gives the exact leading block in every inverse exponential sector
for a single primitive exponential perturbation. Section 9 develops the
inverse of X + log(X) + exp(-X), including rational coefficients, sharp pole
orders, and an all-orders uniform geometric remainder bound. Section 11
contains nine further research questions.

## Scope and status

The main mathematical arguments are human-readable proofs in the article.
The general Hahn and Lagrange mechanisms are classical; the article does not
claim global literature priority or discovery of transseries inversion.
The repository comparison is targeted, not an exhaustive audit of every file.
The bibliography and stable source labels identify the material inspected.

The canonical raw-source web snapshot and live package README were inspected.
Caching and active repository editing can produce different snapshots, so no
unverified commit hash, current TeX/PDF parity, or exhaustive novelty claim
is asserted.

No new Lean, Coq, or other proof-assistant module was compiled. The Python
checks are finite regression tests, not formal proofs. Numerical tests use
high precision but not interval arithmetic; the stated analytic remainder
bound has a separate proof in the article.

## Build the PDF

A standard TeX installation with pdfLaTeX, Latin Modern, and the packages
listed in the source is sufficient. From this directory, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error reversion_and_one_exponential.tex
pdflatex -interaction=nonstopmode -halt-on-error reversion_and_one_exponential.tex
pdflatex -interaction=nonstopmode -halt-on-error reversion_and_one_exponential.tex
```

On a POSIX system, `sh build.sh` performs the three passes. The delivered PDF
was compiled in three final passes with no LaTeX warnings or overfull boxes.
All pages were rendered with Poppler for visual inspection; the cover,
contents, and bibliography were rechecked after the last layout adjustment.

## Reproduce the checks

Python 3.10 or later is required. The recorded run used Python 3.13.5,
SymPy 1.14.0, and mpmath 1.3.0. The dependency versions are pinned in
`requirements.txt`.

```sh
python -m pip install -r requirements.txt
python verify_results.py
```

The program checks mixed rational-exponent reversion modulo t^4, agreement
with three Newton steps in the denominator-6 lattice, and the first six
mixed-example coefficients, their pole orders and leading blocks. It also
checks the defining implicit equation through exponential order six and
compares 24 numerical truncations against the proven error bound.

It writes or replaces `verification_report.txt` and `numeric_checks.csv` in
its own directory. It exits with an exception if an asserted check fails.
It does not access the network, modify the repository, or edit the article.

## Files

- `reversion_and_one_exponential.tex`: complete article source.
- `reversion_and_one_exponential.pdf`: compiled article.
- `verify_results.py`: exact symbolic and high-precision numerical checks.
- `verification_report.txt`: execution receipt and six explicit rational coefficients.
- `numeric_checks.csv`: all 24 numerical comparisons.
- `requirements.txt`: pinned Python dependencies.
- `build.sh`: three-pass PDF build.
- `README.md`: this guide.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed unedited in batch 45 (see `docs/incoming/README.md`).
The following changes were made afterwards; each change to the article is
marked in the source by a `% ed. (2026-09-29)` comment, and every visible
addition is an unnumbered "Editorial note (ProveIt, 2026-09-29)", so no
theorem, question or equation number changed.

- `reversion_and_one_exponential.tex`:
  - Preamble: the unnumbered `ednote` environment.
  - Section 1.1: a footnote giving the current location of the
    `Transseries_And_Inversion` package; the two bibliography entries
    `ProveIt` and `ProveItReadme` now give the current addresses under
    `Analysis/Transseries/docs/series-and-transseries/` instead of the dead
    pre-split path under `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/`.
  - After Theorem 3.2 (`thm:LB`): the same Lagrange sum is proved again by
    the non-Archimedean package `../Reversion_Beyond_Archimedean_Valuations/`
    (`thm:reversion`, `cor:EulerLB`) and by the surcomplex analysis volume's
    `e:lem-reversion`; the term-by-term agreement is stated.
  - After Theorem 4.1 (`thm:newton`): the non-Archimedean package's Newton
    depth law `r ↦ 2r + 1`, `r_n = 2^{n+1} − 1` (`thm:implicit`) is the rate
    `eq:newtonrate` in word-depth units; that package calls it "sharper"
    without citing it, and adds its attainment (`thm:sharp`) and the
    valuation criterion.
  - Section 11, at the questions "Several exponential actions and
    resonances", "Beyond Archimedean exponent groups", 11.8 "Sharp complex
    transition near the core critical point" and "Proof-producing support
    and precision inference": notes saying which later package answers each
    and how far — `../Critical_Transseries_Moving_Fold/` (analytic subclass
    of the first; 11.8 in the independent-parameter chart, the
    fixed-coupling specialization `z = e^{−w}/w` excluded) and
    `../Reversion_Beyond_Archimedean_Valuations/` (the second for
    fixed-shift power–logarithmic derivations only; the algebraic part of
    the last). The Beyond-Archimedean note also names the uncited canonical
    remark `plt:rmk:ext-archimedean`, the surcomplex lemma `e:lem-reversion`
    and the Lean lemmas `Surreal.HahnSeries.finite_words_of_sum_eq` and
    `Surreal.HahnSeries.finite_wordsWithSum`.
- `reversion_and_one_exponential.pdf`: rebuilt from the amended source
  (`latexmk -pdf`): 25 pages, no errors, undefined references, multiply
  defined labels, duplicate destinations or overfull boxes.
- `verify_results.py`: `numeric_checks.csv` is written with an explicit LF
  terminator and `verification_report.txt` with `newline="\n"`, so a rerun
  on Windows no longer reintroduces CRLF. A rerun of the amended program
  (Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0) on a copy reproduced both
  filed outputs byte for byte.
