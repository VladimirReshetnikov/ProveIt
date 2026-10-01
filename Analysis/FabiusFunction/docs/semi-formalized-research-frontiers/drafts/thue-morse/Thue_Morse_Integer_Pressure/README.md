# Integer Pressure and a Missing Taylor Coefficient

**Analytic phase dependence and the sixth-moment optimum for generalized
Thue–Morse products**

Research draft prepared with ChatGPT for Vladimir Reshetnikov, 28 September 2026.

## Contents

- `article.pdf`: complete article, proofs, certificate polynomials, bibliography,
  and nine proposed research questions.
- `article.tex`: self-contained LaTeX source; no repository checkout needed.
- `verify_pressure.py`: exact finite matrix, moment, and Taylor checks.
- `verification.json`: executed receipt for the default 23 test groups.
- `verify_minimum.py`: exact characteristic-polynomial, resultant, subresultant,
  Sturm, rational interval, and low-order comparison checks.
- `minimum_certificate.json`: executed sixth-moment minimization certificate.
- `requirements.txt`, `Makefile`: optional build and verification convenience.
- `source_manifest.json`: inspected source versions and provenance.
- `CLAIMS_AND_VALIDATION.md`: scope, dependency boundaries, and validation status.

## Main results

For T(x)=2x mod 1 and g_c(x)=cos²(pi(x-c)), let p_m(c) be the natural-log
pressure of m log g_c. For every positive integer m, the article proves that
p_m is a real-analytic function of c on the circle, identifies it with the
logarithm of a simple eigenvalue of an explicit (2m-1)-dimensional matrix,
and proves a phase-uniform exponential error in the moment asymptotic for
fixed m.

The article also proves that the coefficient of c^(2m) in p_m(c) is zero.
It explains the cancellation by an exact two-branch eigenvalue equation and
a periodized-sinc Perron function at c=0.

For the fourth moment, the classical phase c=1/2 is the unique minimizing
phase. For the sixth moment it is a strict local maximum instead. The two
global sixth-moment minimizers are c* and 1-c*, with
c* approximately 0.364919195551255. The cosine parameter cos(2*pi*c*) is
specified exactly by a degree-14 polynomial and a rational isolating
interval. The proof does not rely on numerical optimization.

## Build

A standard TeX Live installation with Libertinus, AMS, microtype, hyperref,
and cleveref is sufficient:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

For the computation, use Python 3.10 or later and SymPy:

```sh
python -m pip install -r requirements.txt
python verify_pressure.py
python verify_minimum.py
```

SymPy 1.14.0 was used for the supplied receipts. The scripts use exact
rational or Gaussian-rational arithmetic for all assertions. Do not run
with `python -O`, which would disable assertions. They overwrite their
respective JSON receipts in the current directory. The pressure checker
accepts `--max-m` and `--output`; run `--help` for details.

## Scope and status

The all-integer phase theorem addresses the integer slice of the regularity
question following Theorem 2.7 of Gohlke–Kesseböhmer–Schindler,
arXiv:2509.22109v1. Noninteger orders remain outside the theorem.
Classical moment recurrences and the original order-two analyticity result
are prior work, not discoveries claimed by this package.

The proofs are research arguments, not independently refereed results.
The exact scripts have been run successfully; no Lean proof or Lean build
is claimed. The measure-theoretic dimension corollaries use the cited
external pressure–spectrum identity. Priority of the proposed new results
has not been independently established.

The relevant ProveIt content was inspected at commit
37e61c1fdec28c6e7ab7ff445043993077b42cbd. The remote repository was not modified.

## Editorial amendments (ProveIt, 2026-09-30)

In the editorial pass after batches 66 to 68 of `docs/incoming/` (see
`docs/incoming/README.md`), a later package of this tree was found to bear on
one of its research questions. The mathematical text is unchanged; every
change to the source is marked `% ed. (2026-09-30)`.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note
  (ProveIt, 2026-09-30)") is defined after the last theorem style. After
  Question 12.7 ("Beyond one zero and beyond base two") and its discussion,
  a note records that
  `../Periodic_Anchors_Exact_Mixed_Moment_Phase_Diagrams/` (batch 68, unreviewed) computes exactly the pressure of products of shifted digital
  masks whose phases fill complete periodic orbits of `x -> bx mod 1`, with
  a common exponent on each orbit, with every equilibrium measure, in every
  base; it bears on the question without answering it (fixed phases; a
  single mask whose phase has period at least two is not covered; no
  phase regularity); it adds that such a product's zeros all map onto the
  selected orbits and that no finite Perron model or spectral simplicity is
  proved there.
- `article.tex`: the title page no longer sets hyperref page anchors (it is
  numbered 1 like the following page), which removes the delivered source's
  one duplicate-destination warning (`page.1`).
- `article.pdf`: rebuilt with `latexmk -pdf -interaction=nonstopmode
  -halt-on-error article.tex` (MiKTeX pdfTeX 1.40.29): 25 pages (24 as
  delivered; the note adds one), with no error, undefined reference,
  multiply defined label, duplicate destination or overfull box; no Type 3
  font. The page carrying the note was rendered and inspected.

## Editorial amendments (ProveIt, 2026-10-01)

In the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`), thirteen later packages filed beside this article
(`../Thue_Morse_Integer_Pressure_*/`; listed in the README of `../`) were found
to answer its question "The first coefficient after the cancellation". The
mathematical text is unchanged; every change to the source is marked
`% ed. (2026-10-01)`.

- `article.tex`: a second unnumbered environment `ednotelater` ("Editorial
  note (ProveIt, 2026-10-01)") is defined after `ednote`. After Question 12.2
  ("The first coefficient after the cancellation") and its discussion, a note
  records that `../Thue_Morse_Integer_Pressure_First_Positive/` proves
  `[t^{2m+2}]p_m(t/pi) > 0` for every integer `m >= 2`, along the route the
  discussion suggests, with the finite formula
  `sum_{j=1}^{m-1} b_{m,j} R_{m-j} + (2m/3) R_m - m/(m+1) R_{m+1}`, the
  `b_{m,j}` explicit positive rationals built from Bernoulli numbers (a closed
  form in that finite sense; no elementary closed form, and the reduced
  denominators are left open), which overtakes "The executed checks are
  positive for 2 <= m <= 6"; that every even coefficient strictly between
  degrees `2m` and `6m` is positive for every `m >= 2`
  (`../Thue_Morse_Integer_Pressure_Full_Range/`), where `6m` cannot be included
  in general since `[t^12]p_2(t/pi) = -35360872/93555`; and that the first
  negative degree `N_m` above `2m` satisfies
  `N_m = gamma m - log log(2m)/Lambda + O(1)`, `gamma` in
  `(6.662966, 6.662968)` (`../Thue_Morse_Integer_Pressure_First_Negative/`),
  certified for `2 <= m <= 128`
  (`../Thue_Morse_Integer_Pressure_First_Negative_Data/`). The packages
  confirm this article's results: the first one re-derives the feedback
  identity behind the cancellation `[c^{2m}]p_m = 0` and reproduces the three
  coefficients of (8.5)-(8.7). No
  other question of Section 12 is answered by them; "Quantitative gaps and
  certified errors" concerns the constants of the moment estimate, which they
  do not treat.
- `article.pdf`: rebuilt with `latexmk -pdf -interaction=nonstopmode
  -halt-on-error article.tex` (MiKTeX pdfTeX 1.40.29), on a copy: 25 pages
  (as before), 787,321 bytes, with no error, undefined reference, multiply
  defined label, duplicate destination, overfull or underfull box; no Type 3
  font. The page carrying the note was rendered and inspected.
- `README.md`: this section.
