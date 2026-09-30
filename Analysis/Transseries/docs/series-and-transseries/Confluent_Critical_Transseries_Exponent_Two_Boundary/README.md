# Confluent Critical Transseries Across the Exponent-Two Boundary

A Uniform Inverse Chart, Conditional Poisson Limits, and Sharp Action Budgets

Research draft prepared for Vladimir Reshetnikov, 29 September 2026.

## Contents

- `Confluent_Critical_Transseries.pdf`: 24-page article (23 pages as delivered;
  rebuilt on filing, see the amendments below).
- `Confluent_Critical_Transseries.tex`: main LaTeX source.
- `data/coefficient_table.tex` and `data/inversion_table.tex`: included table fragments.
- `code/verify.py`: exact algebraic checks and numerical diagnostics.
- `data/*.csv`: reproducible numerical data.
- `data/*checks.json` and `data/run_all.json`: recorded checks and package versions.
- `SOURCES.md`: repository snapshot, research target, and reference provenance.
- `BUILD_VALIDATION.json`: compilation, rendering, and test status.

The delivered checksum ledger `SHA256SUMS` was verified in full on filing
(batch 49) and not kept; the delivered archive remains in the repository
history (see `docs/incoming/README.md`, batch 49 row).

## Mathematical scope

The main model is

    U_e(q) = c_e sum_{j>=1} j^(-3+e) q^j exp(j U_e(q)),
    c_e = 1/zeta(2-e).

The article addresses the upper-endpoint joint-limit part of Research
Question 4 in the repository's critical-Hahn/countable-action article:
coefficient order n tends to infinity while the exponent alpha=2-e tends
to 2. The sequence e_n may have either sign, change signs, and approach zero
at any rate. The fixed endpoint was already treated in earlier drafts.

The main results are:

1. A single convergent holomorphic correction chart over the exact core
   c_e r^2 h_e(1/r)/2 = delta, including explicit first and second homogeneous
   terms, a finite coefficient recurrence, and a geometric Taylor remainder.
2. An arbitrary-rate triangular local Gaussian theorem, uniformly stable
   under all tail-thinning masks that retain actions up to a positive fixed
   multiple of the extreme-action scale.
3. Multiplicative sector asymptotics and the sharp prefix-cutoff profile
   R_n(M) -> exp(-1/(2s^2)) when M/A_n -> s, with a necessary-and-sufficient
   condition for asymptotically retaining the full coefficient.
4. A conditional Poisson point-process limit with intensity y^(-3) dy, valid
   under exact lattice conditioning, not only unconditional weak convergence.
5. Explicit exponent/order crossover formulas, a bounded moving-coupling
   window, finite-prefix robustness, and the exact identity r_e(1/(2n))=1/B_n.

Here

    h_e(x) = (x^e-1)/e, with h_0(x)=log(x),
    A_n = (n c_e)^(1/(2-e)),
    B_n^2 = n c_e h_e(B_n), with B_n the large positive root.

The article contains 19 numbered theorems, propositions, lemmas, and
corollaries, with conventional proofs, plus 12 further research directions.

## Status and limitations

Theorems are proved in ordinary mathematical prose. No Lean formalization is
included or claimed. Publication priority has not been established by an
exhaustive literature search. The fixed cubic-tail Gaussian/extreme-value
mechanism has classical antecedents, explicitly credited in the article.

The analytic chart is convergent to all orders. The triangular coefficient
asymptotic is leading order; an all-order uniform coefficient correction
calculus is left as a further research problem. The lower endpoint alpha=1,
complex global continuation, general resurgence, arbitrary slowly varying
triangular tails, and growing coupling windows are not covered.

The program's exact checks verify finite algebraic identities. Its numerical
checks use floating-point and arbitrary-precision arithmetic, not interval
arithmetic. A small computed residual is not presented as a root enclosure.
The article proves separate real inequalities suitable for an eventual
outward-rounded implementation. Cauchy polydisc constants exist by the proof;
certified numerical radii for that polydisc have not been computed.

## Build the PDF

The included table fragments allow compilation without running Python.
A standard TeX Live installation with `latexmk` and `pdflatex` is sufficient:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error Confluent_Critical_Transseries.tex
```

Alternatively, run `pdflatex` three times. No bibliography processor, custom
font installation, external style file, or network access is needed for the
LaTeX build. The complete ZIP, rather than the main TeX file alone, contains
the table dependencies.

## Run the checks

The recorded environment was Python 3.13.5, NumPy 2.3.5, SymPy 1.14.0,
and mpmath 1.3.0. Install the pinned dependencies and run:

```sh
python -m pip install -r requirements.txt
python code/verify.py --part all
```

The three groups can be run separately:

```sh
python code/verify.py --part exact
python code/verify.py --part coefficients
python code/verify.py --part inversion
```

Do not pass Python's `-O` option: the exact checks intentionally use assertions.
Running the program overwrites the corresponding CSV, JSON, and table files
inside `data/`, including the two tables the article inputs, and a run of a
single part also writes a new `data/run_<part>.json`. Since filing,
`--output-dir DIR` sends every output to `DIR` instead; use it, or a copy of
the package, for reruns. The recorded data are included so that the article
remains readable and compilable without rerunning any diagnostics.

The large-order probability recurrence uses extended-range `numpy.longdouble`.
On platforms where `longdouble` has the same exponent range as binary64
(including some Windows installations), the program raises a clear error
rather than underflowing. The exact and inversion groups remain usable there;
the independent `poisson_mass_mp` function supports smaller arbitrary-precision
probability audits. Large-order coefficient runs on such systems require an
environment with extended-range long double, such as a suitable Linux/WSL
installation, or adapting the arbitrary-precision recurrence with the
corresponding runtime cost.

On Windows (2026-09-29, on a copy) `--part exact` and `--part inversion`
passed and reproduced `exact_checks.json`, `inversion_checks.json`,
`inversion_diagnostics.csv` and `inversion_table.tex` byte for byte;
`--part coefficients` stopped with the documented `RuntimeError` before
writing anything, so the recorded coefficient data could not be regenerated
there.

## Recorded outcomes

- 122 exact assertions passed.
- Nine coefficient/cutoff diagnostic rows, through n=8192.
- Six independent arbitrary-precision recurrence comparisons; maximum relative
  disagreement about 7.122e-18.
- Nine 160-digit inverse-chart tests; evaluated relative equation residuals
  below 1e-55.
- PDF compiled with zero undefined references/citations and zero overfull boxes.
- All pages were rendered; page layouts were reviewed in contact sheets and
  selected pages at larger size.

None of the numerical tests is a proof of an asymptotic limit. No repository
files were modified.

## Editorial amendments (ProveIt, 2026-09-29)

These changes were made on filing, after the batch-49 delivery. Every change
to the article text is marked in `Confluent_Critical_Transseries.tex` by a
comment beginning `% ed. (2026-09-29)`; visible additions are headed
"Editorial note (ProveIt, 2026-09-29)" or, in the bibliography, "[Editorial
addition, ProveIt, 2026-09-29.]".

- `Confluent_Critical_Transseries.tex`:
  - an unnumbered `ednote` environment for editorial notes (no numbering
    changes);
  - an editorial note in Section 1.1: the two drafts it read from the
    library are now filed as the logarithmic-endpoint and marginal packages,
    each of which lists this joint limit as its Question 1; this article
    answers the chart and leading-order parts of both, for every rate, but
    not the uniform first cutoff correction; the stable–Gaussian package
    filed with it answers the same question independently in the window
    `|eps| log n <= K`, one order further, and the two agree term by term
    (scales, window forms, minimal budget, profile, conditioned Poisson
    limit);
  - the filed locations of the two drafts in their bibliography entries, and
    an editorial bibliography entry `ed:sge`.
- `Confluent_Critical_Transseries.pdf`: rebuilt from the amended source
  (24 pages; the delivered PDF had 23). `BUILD_VALIDATION.json` still
  describes the delivered build.
- `code/verify.py`: every CSV, JSON and table output is written with LF line
  endings (the CSV writer emitted CRLF on every platform, `write_text` CRLF
  on Windows); new option `--output-dir`. The default behaviour is otherwise
  unchanged.
- `README.md`: the retired checksum ledger is no longer listed; rerun
  behaviour and the Windows rerun documented; page count updated; this
  section.

### Batch-51 cross-reference notes (ProveIt, 2026-09-29)

Added when batch 51 was filed; marked in the source by `% ed. (2026-09-29)` comments.

- `Confluent_Critical_Transseries.tex`: an editorial note at Question 10
  ("The lower endpoint"): partly answered, for the pure tail `j^(-2-eps)` on
  the interior-fold side (couplings above `1/zeta(1+eps)`), by
  `../Lower_Critical_Endpoint_Landau_Transseries/` (batch 51; a compensated
  core uniform through `eps = 0`, and conditioning that couples a large
  action to a doubly exponentially unlikely compensating fluctuation); the
  boundary-critical side, where this article's coupling `c_eps = 1/zeta(alpha)`
  lies, remains open. A new editorial bibliography entry `ed:lcl`, appended
  last. The statement above that the lower endpoint is not covered by this
  article stays true.
- `Confluent_Critical_Transseries.pdf`: rebuilt (24 pages, unchanged; no
  errors, undefined references, multiply defined labels or duplicate
  destinations).
