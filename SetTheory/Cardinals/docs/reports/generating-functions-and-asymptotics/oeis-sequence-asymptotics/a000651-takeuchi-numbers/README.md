# Asymptotic Expansions of the Takeuchi Numbers

**OEIS A000651: a proof of `log T_n = F(n) + g(w) + log C + p_1(w)/n +
p_2(w)/n² + O((1+w)^8/n³)`, `w = W(n)`, an every-fixed-order hierarchy, an
explicit third coefficient, and controlled real and integer inverses**

A research report dated 1 October 2026, built from one manuscript. Its author
line reads only "A self contained research report" (PDF metadata author:
"Research report"); the delivery names no author and no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 65 | `takeuchi-asymptotics-research.zip` (wrapper directory `takeuchi-asymptotics/`), arrival commit `096ee7b87`; main file `takeuchi-asymptotics.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `34f1acd4b` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor a
tool), unrefereed ("a research manuscript, not a peer-reviewed publication"),
not formalized: no Lean or Rocq declaration exists for any statement of this
report. Exact SymPy scripts corroborate the finite algebraic identities; the
analytic remainders and the coupling argument rest on the written proof. The
leading equivalent is Prellberg's (announced 2002); no priority is claimed for
any displayed formula.

## What it proves

`T_n` are the Takeuchi numbers (0, 1, 4, 14, 53, 223, 1034, …), defined by
Knuth's positive recurrence `T_n = Σ_{k<n} c(n,k) T_{n−k−1} + b_n`. Put
`w = W(n)`, `F(n) = e^w (w² − w + 1)`, `g(w) = w²/2 − ½ log(1+w)`.

- **Theorem 1.1 (two corrections).** `log T_n = F(n) + g(w) + log C +
  p_1(w)/n + p_2(w)/n² + O((1+w)^8/n³)` with explicit rational `p_1`, `p_2`
  and `C = lim T_n exp{−F(n) − g(W(n))} ∈ (0,∞)`. The proof does not assume
  the previously announced leading equivalent.
- **Theorem 1.2 (every fixed order).** Canonical smooth `p_j` of polynomial
  growth, each given by a finite exact algorithm and one convergent quadrature,
  with error `O_J((1+w)^{A_J}/n^{J+1})` and the same `C` at every order.
- **Lemma 4.1 and Corollary 4.2 (descending-chain coupling).** A quantitative
  stability theorem for descending Markov chains whose jumps are close to
  `1 + Pois(W(r))`, with atomic endpoint-coupled smoothing blocks; this is the
  transfer from a local recurrence defect to the true sequence.
- **Corollary 8.1 (three corrections).** Explicit rational `p_3`
  (`p_3(w) ~ w^4/72`, so `p_j = O(w^j)` fails at `j = 3`) and error
  `O((1+w)^10/n^4)`.
- **Section 9 (Bell comparison).** With `C_T = eC`, the Takeuchi-minus-Bell
  coefficients `r_1`, `r_2`, and Prellberg's historical first-correction form.
- **Propositions 10.1 and 10.2, and (50), (53) (inversion).** Explicit
  reversion of the finite model with absolute error tending to zero, a finite
  Newton hierarchy with error `O((1+ω)/v^(2^r − 1))`, real localization
  `x_J(T_n) = n + O(…)`, and the two-ceiling bracket for
  `N(y) = min{n : T_n ≥ y}`.
- **Section 2.1 (external sources).** The broad theorem printed in Prellberg's
  2002 slides and the seminar summary omits a restriction: `f = z/(1−z)`,
  `a = z`, `b = 1` gives `X_n = B_{n−1}`, not a nonzero multiple of `B_n`.
  This is the manuscript's claim about published sources; it does not affect
  the Takeuchi application (`a = f`).

## What is not claimed

- No priority for the leading equivalent (Prellberg 2002, also Mishna's
  seminar summary, Section 3.2) or for the existence of earlier formal higher
  terms; the literature search "is not proof of absence of another correction
  theorem".
- `C` is not numerically enclosed; Prellberg's decimal `C_T ≈ 2.2394331040…`
  is used only in labelled, non-certified diagnostics.
- No convergence of the infinite expansion, no rationality of every `p_j`, no
  exponentially small terms, no unconditional exact rounding of the inverse
  for arbitrary targets; the inverse statements use the exact `C`.
- The remaining questions of Section 11 (effective constants, sharper
  transfer, coefficient structure, optimal truncation, constant formulas,
  specialist review of the 2002 hypotheses) are open.
- **The inversion is an instance of repository results; no novelty is claimed
  for the method.** Localization by dividing a log error by the slope is
  `p0:thm:backward-error`; the two-ceiling bracket has the form of the
  separation condition, part (2) of `p0:thm:staircase`, and the remark on
  targets equal to some `T_n` is its part (3); the explicit reversion is a
  first-order perturbative reversion of the kind `p0:thm:perturbed-inversion`
  treats. All are in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  The leading equation `e^ω(ω²−ω+1) = t` is not of the
  `p0:thm:lambert-core` form. A dated `[write]` note at the end of Section 10
  says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
and its place in the collection gives it no formal status; the manuscript used
no ProveIt theorem. The generic staircase arithmetic named in the Section 10
note is formalized as `Fabius.staircase_ceil` and `Fabius.staircase_separation`
in `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; those
lemmas concern an arbitrary monotone function, not `T_n`.

**Neighbouring reports** (same directory, `oeis-sequence-asymptotics/`):

- `a277364-bell-asymptotics` proves `B_n = F(n)(1 − P(r)/n + …)` with
  `r = W_0(n)`; since `n = re^r`, `−P(r)/n = b_1(r)e^(−r)`, so the first Bell
  coefficient quoted here (Prellberg 2000, eq. (12)) agrees with it. Its `F(n)`
  is the Bell leading term, not this report's `F(n) = e^w(w²−w+1)`. Neither
  report uses the other. Dated note in Section 9.
- `a139383-iterated-bell-diagonals` (batch-77 iterated-Bell manuscripts,
  placed in `aa7345800`) gives the same check of Prellberg's printed general
  theorem; its proportional-depth addendum's literature note (shipped there as
  `28-proportional-sources-literature.md`) quotes
  Section 2.1 of this manuscript by an unshipped `/workspace/shared/…` path,
  and its attribution review checked the limitation against this report.
  That report, as written, keeps its own one-paragraph copy of the check
  (Part I, subsection "Historical attribution", with a note pointing here),
  so the check is printed in both reports and the two agree (dated notes in
  Section 2.1; the second, batch 77P2, corrects the first's "printed once,
  here"). That report treats the bivariate iterated-Bell numbers, not `T_n`.

(These pointers were made here only; the neighbouring reports were not
edited by this write. The batch-77P2 reciprocal notes later added a dated
note to `a277364-bell-asymptotics`, after its remark "Two normalizations",
pointing back here; `a139383-iterated-bell-diagonals` already pointed here.)

## Notation

The manuscript reuses letters with section-local meanings (`B` four ways; `a`,
`b`, `c`, `d`, `v`, `u`, `h`, `H`, `J`, `L`, `P`, `Q`, `A`, `K`, `M` two or
three ways each; the manuscript itself warns about `v`). A table in the first
`[write]` note (end of Section 1) fixes each symbol by section, with the
tempting false readings, including the clash of `F(n)` with the Bell report.
No symbol was renamed.

## Labels

Every label carries the prefix `tak:`. The manuscript's 70 labels were
prefixed before anything cited them (every `\ref`/`\eqref` updated), and two
section labels (`tak:sec:results`, `tak:sec:limitation`) were added for the
notes: 72 labels in all. The writing step also added five dated `[write]`
notes (Section 1: provenance and notation table; Section 2.1: the
external-source claim and the iterated-Bell duplicate; Section 9: the Bell
report; Section 10: the transseries-instance note; Section 11: the shipped
layout), and loaded `booktabs` and `array` for the table. A sixth dated note
(Section 2.1, batch 77P2) was added afterwards with the reciprocal notes: it
corrects the first Section 2.1 note's claim that the Prellberg check is
printed only here. No statement, proof or number of the manuscript was
changed.

## Files

```text
README.md                               this guide (replaces the delivery README)
article.tex                             the report (delivered as takeuchi-asymptotics.tex)
article.pdf                             compiled report, 19 pages
receipts-QA.md                          delivered artifact-verification receipt (delivery paths; see below)
receipts-mathematical-review.md         delivered integrated mathematical review (tied to the delivered TeX hash)
receipts-third-coefficient-review.md    delivered review of the third coefficient
receipts-inverse-review.md              delivered review of the inversion section
code/derive_residual.py                 arbitrary-fixed-order exact residual generator
code/test_generator.py                  exact regression tests of the generator
code/check_two_coefficients.py          p_1, p_2 derivation and cancellations
code/check_bell_comparison.py           independently differentiated residuals; Takeuchi-minus-Bell identities
code/check_independent.py               independent fourth-order check of H_3
code/check_third_literal.py             literal check of H_3, p_3 and growth degrees
code/check_inverse.py                   inverse reversion and derivative bounds
code/check_numeric.py                   exact T_n and non-certified diagnostics
code/replay.py                          delivered one-command replay (needs the unshipped SHA256SUMS; see below)
code/build.sh                           delivered PDF build (compiles takeuchi-asymptotics.tex beside it)
data/receipts-check_two_coefficients.log  recorded output of check_two_coefficients.py
data/receipts-check_bell_comparison.log   recorded output of check_bell_comparison.py
data/receipts-derive_residual.log         recorded output of derive_residual.py
data/receipts-test_generator.log          recorded output of test_generator.py
data/receipts-check_independent.log       recorded output of check_independent.py
data/receipts-check_third_literal.log     recorded output of check_third_literal.py
data/receipts-check_inverse.log           recorded output of check_inverse.py
data/receipts-check_numeric.log           recorded output of check_numeric.py
data/receipts-result-recomputed.json    derive_residual.py --include-p3 --order 5 result
data/receipts-numeric-recomputed.json   check_numeric.py --max-n 1500 result
data/receipts-replay-summary.json       delivered replay summary (commands, exit codes, times)
data/receipts-environment.txt           Python 3.12.14, SymPy 1.14.0, mpmath 1.3.0, Linux
data/receipts-build-smoke.txt           isolated rebuild record
data/receipts-latex-final.log           final LaTeX log of the delivered PDF
data/requirements.txt                   sympy>=1.12,<2 and mpmath>=1.3,<2
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed `takeuchi-asymptotics.tex`
to `article.tex`, moved `replay.py` and `build.sh` to `code/`, the run outputs
of `receipts/` to `data/receipts-*`, the four Markdown records of `receipts/`
to `receipts-*.md` in this directory, and `requirements.txt` to `data/`.
Not shipped: the delivered 17-page PDF `takeuchi-asymptotics.pdf` and
`SHA256SUMS` (a checksum ledger, verified 32/32 at placement and retired).
Both survive in the archive:
`git show 096ee7b87:docs/incoming/takeuchi-asymptotics-research.zip > <scratch>/takeuchi-asymptotics-research.zip`.
Nothing heavy was excluded.

Delivered text that names the delivery layout or unshipped files:
`code/replay.py` (reads `SHA256SUMS` beside itself and raises if it is
missing; copies `code/` into a work directory; with `--build-pdf` compiles
`takeuchi-asymptotics.tex` and compares with `takeuchi-asymptotics.pdf`),
`code/build.sh` (compiles `takeuchi-asymptotics.tex`, writes `receipts/` and
`.build/` beside itself), `receipts-QA.md` (`receipts/…`, `replay.py`,
`SHA256SUMS`, the delivered PDF's hash), the three review records (hashes of
the delivered TeX and PDF), and Section 11 of the article (dated note). The
review hashes refer to the delivered `takeuchi-asymptotics.tex`, which is the
`article.tex` of the placement commit `34f1acd4b`, not the written one. The
delivery README, which this guide replaces, said the Bell check "can take a
few minutes"; its receipt records 132.6 s.

## Rerun the checks (on a scratch copy)

`replay.py` cannot run as shipped (no `SHA256SUMS`), and two commands write
into `receipts/`. Run the eight commands of its list on a copy (Git Bash, from
this directory):

```sh
R=$(mktemp -d) && mkdir -p "$R/code" "$R/receipts" && cp code/*.py "$R/code/" && cd "$R"
export PYTHONUTF8=1
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY code/check_two_coefficients.py > receipts/check_two_coefficients.log
$PY code/check_bell_comparison.py > receipts/check_bell_comparison.log
$PY code/derive_residual.py --include-p3 --order 5 --output receipts/result-recomputed.json > receipts/derive_residual.log
$PY code/test_generator.py > receipts/test_generator.log
$PY code/check_independent.py > receipts/check_independent.log
$PY code/check_third_literal.py > receipts/check_third_literal.log
$PY code/check_inverse.py > receipts/check_inverse.log
$PY code/check_numeric.py --max-n 1500 --output receipts/numeric-recomputed.json > receipts/check_numeric.log
for f in receipts/*; do diff -q --strip-trailing-cr "$f" "$OLDPWD/data/receipts-${f#receipts/}"; done
```

Expected differences: elapsed-time fields only (`numeric-recomputed.json`
records its run time). At intake (2 October 2026, heavily loaded machine)
seven commands passed with identical output (7.6–50 s each);
`check_bell_comparison.py` exceeded the 170-second limit there (receipt:
132.6 s) and passed when split into its two halves, with output identical to
the receipt. Windows writes CRLF, hence `--strip-trailing-cr`. For the
one-command replay, recover `SHA256SUMS` from the archive and rebuild the
delivered layout (`replay.py`, `build.sh`, `requirements.txt`,
`takeuchi-asymptotics.tex`, `code/`, `receipts/`) on a copy; it writes under
`.replay/` beside itself.

## Build the PDF

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, microtype, hyperref, xcolor,
enumitem, fancyhdr, lmodern, booktabs, array); no BibTeX. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 19 pages, no
errors or warnings, no undefined references or citations, no multiply defined
labels, no duplicate PDF destinations, no overfull or underfull boxes. (The
delivered source built to 17 pages, also clean.) `code/build.sh` is kept as
delivered; to use it, copy it to a scratch directory together with
`article.tex` renamed to `takeuchi-asymptotics.tex`.

## Provenance

- Prellberg, arXiv:math/0005008 (2000), Eqs. (3), (12), Conjecture 1;
  Prellberg, FPSAC 2002 slides 22, 25, 26; Mishna's summary of Prellberg's
  seminar of 23 September 2002, INRIA Algorithms Seminar 2002–2004, pp. 47–50;
  Knuth, "Textbook examples of recursion" (1991); OEIS A000651.
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 65 (cluster P3); arrival
  `096ee7b87`, placement `34f1acd4b`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
