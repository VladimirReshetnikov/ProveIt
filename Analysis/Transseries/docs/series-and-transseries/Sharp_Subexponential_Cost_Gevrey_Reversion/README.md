# Sharp Subexponential Reversion

**Exact extremal cost, a Gevrey transition, and composition of two divergent series**

Prepared for Vladimir Reshetnikov, 29 September 2026.

The package contains a 23-page research article (22 pages as delivered), its LaTeX source, exact finite
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
multiplicative equivalent. (Editorial, 2026-09-30: the complete equivalent at
every positive order, including the constant at s = 1/3, and the lower
transition windows are supplied by
`../Finite_Jet_Pressure_Laws_Gevrey_Reversion/`; see the amendments below.) The composition theorem is for factorial powers,
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
To regenerate the printed tables from a diagnostic run and compare them with
the article's inputs `data/*_table.tex`:

    python code/render_tables.py --input data/rerun --output data/rerun

The supplied tables were generated from `data/recorded`; `render_tables.py`
with no arguments re-renders them from there into `data/rerun`. (As
delivered, both the default and this documented command wrote into `data/`,
overwriting the article's table inputs; see the amendments below.)

## Files

* `article.tex`, `article.pdf`: article source and compiled PDF.
* `code/verify.py`: exact finite tests and optional numerical diagnostics.
* `code/render_tables.py`: deterministic CSV-to-LaTeX table rendering.
* `data/recorded/`: original check ledger and numerical CSVs.
* `data/*_table.tex`: supplied article tables.
* `data/build_validation.json`: compile, geometry, font, and visual checks.
* `provenance.json`: snapshot, source paths, and scope.

No repository or persistent Library file is modified by this package.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 52 (see `docs/incoming/README.md`). The
following changes were made on 2026-09-29; everything else is as delivered.

- `article.tex`: an unnumbered `ednote` environment (the article's remarks
  share the theorem counter, so its numbering is unchanged) and four visible
  "Editorial note (ProveIt, 2026-09-29)" paragraphs, each preceded by a
  `% ed. (2026-09-29)` comment, recording the companion package of the same
  batch, `../Exact_Weighted_Type_Beyond_Log_Convexity/`, written
  independently from an earlier snapshot:
  - end of Section 1.2: that package proves the maximum law of
    Theorem 8.1 (`thm:composition`) for every weight subexponentially
    equivalent to a supermultiplicative weight with superexponential roots,
    with the full equal-type spectrum `[0, T]`; Section 8 is its factorial
    case, proved here by a different majorant (one theorem, two independent
    proofs). The fixed-ball results are not in that package;
  - after the phase diagram `eq:phase`: with `A = 1`, `G_*` is that
    package's extremal inverse `H_C` for `N_j = w_j`; it proves
    `log R_n = o(n)` for every weight with superexponential roots and asks
    for the optimal overhead, which Theorem 2.2 (`thm:main`) answers for
    factorial weights;
  - at the questions "Two divergent inputs for general weights" (answered
    there) and "Several variables and operator-valued coefficients" (its
    type-level part is there; the fixed-ball problem stays open).
  Two hygiene fixes, also marked: the title page no longer creates a PDF
  page anchor (removing the delivered build's duplicate destination
  `page.1`), and the title of Section 5 uses `\texorpdfstring` (removing two
  hyperref warnings). No label was renamed or removed.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf`
  (23 pages; the delivered PDF had 22; no errors, undefined references,
  multiply defined labels, duplicate destinations or overfull boxes).
  Line numbers of `article.tex` after line 27 differ from the delivered file.
- `data/build_validation.json`: `pdf_pages` recomputed; an
  `editorial_rebuild` field says so; its other fields describe the
  delivered build.
- `code/verify.py`: both CSV writers pass `lineterminator='\n'` (the csv
  default is CRLF on every platform, which is why the delivered
  `data/recorded/*.csv` had CRLF line endings) and the JSON writer
  `newline='\n'`; the default `--order` is now 45, the order of the recorded
  run and of every documented command (it was 40).
- `code/render_tables.py`: writes LF on every platform, and its default
  `--output` is `data/rerun` instead of `data`, so a bare run no longer
  overwrites the article's table inputs; this README's regeneration command
  now writes to `data/rerun` too.
- `data/recorded/crossover.csv` and `data/recorded/diagnostics.csv` were
  delivered with CRLF line endings and are filed with LF (same content).
- Windows stop: NumPy on Windows has no extended-range `longdouble`, so
  `--diagnostics` (and hence `--mp-check`, which calls the same routine)
  stops with `RuntimeError: Diagnostics require an extended-range NumPy
  longdouble.` The recorded diagnostics therefore cannot be regenerated on
  this machine. On filing, a float64 recomputation with log-scaled ratios
  (not shipped) reproduced every printed table entry to six decimals and
  every recorded CSV value to a relative 5e-13; run through the amended
  writers, it produced LF CSV files with the recorded headers and row counts.
- Rerun on a copy (Windows, `py code/verify.py`): 5,338 scalar checks and
  512 sign patterns passed; `data/rerun/verification.json` is byte-identical
  to the recorded ledger with its two diagnostic keys (`diagnostics`,
  `high_precision_cross_checks`) removed. `py code/render_tables.py`
  reproduced both `data/*_table.tex` files byte for byte. The documented
  commands use bare `python`; on Windows use `py`.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batch 65 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`. The byline is kept as delivered, as before.

- `article.tex`: a second unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" (`ednotelater`) is defined in the preamble. Three notes
  record the later package `../Finite_Jet_Pressure_Laws_Gevrey_Reversion/`
  (batch 65, written against this article as amended):
  - in Section 1.2, after the statement that a complete multiplicative
    equivalent remains open for `0 < s < 1/2`: its Theorem `thm:main` gives
    `log R_n = sum_{k<=J} p_k n^(1-ks) + o(1)` for `(J+1)s > 1`, with an
    explicit coefficient formula, for these weights and for eventually
    shifted-factorial weights with an arbitrary positive finite head; it
    recovers `eq:multmain` and `eq:halfmain`; its `o(1)` is not effective
    and not uniform as `s -> 0`;
  - at the question "Complete multiplicative cost below one half":
    answered for every `0 < s < 1/2`; at `s = 1/3` the constant is
    `6^(1/3) C + (5/3) 2^(1/3) C^2 + 7 C^3/9`;
  - at the question "Uniform transitions at the lower thresholds": answered
    by its Theorem `thm:windows` (which does not claim the question):
    for `s_n = 1/r + t/log n`, after the moving lower terms are subtracted,
    `log R_n -> p_r(1/r) e^(-rt)` uniformly for bounded `t`; its `r = 1`
    case is `eq:crossover`; the remainder is not effective.
  No label was renamed or removed.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf`
  (MiKTeX pdfTeX 1.40.29): 23 pages, as after the first pass, with no
  error, undefined reference, multiply defined label, duplicate destination,
  or overfull box; every font is embedded and none is Type 3. The pages
  carrying the notes were rendered and inspected.
- `data/build_validation.json`: its `editorial_rebuild` field gains a
  sentence on this rebuild.
- `README.md`: the pointer under "Boundaries", this section, and three
  repaired code spans in the 2026-09-29 section, whose backslashes had been
  lost on writing: `\texorpdfstring` (it held a tab character),
  `lineterminator='\n'` and `newline='\n'` (each held a line break).
