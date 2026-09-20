# A mixed-base counterexample to Stanley's rationality question

This package contains a 32-page article with self-contained proofs, editable
LaTeX source, exact-integer Python code, verification results, and sequence data.

**Provenance.** This report merges two independently produced research reports
on the same question, originally distributed as the directories
`mixed-base-rationality-classification` and `mixed-base-natural-boundary`.
The shared enumerative core was proved by the same argument in both and is
proved once here. Where the two genuinely diverged, both arguments are kept and
marked: the elementary mod-p obstruction (Section 4) beside the finite-quotient
rigidity theorem (Section 5), and the direct Cesaro natural-boundary
computation beside the general irrational-floor theorem (Section 8).
Section 1.2 of the article states this in full.

## Main result

Set `G_(2j+1) = 2^j`, `G_(2j+2) = 3^j`, and
`P_N(x) = product_(i=1..N) (1 + x^(G_i))`.
The exponent generating function is rational:

    sum_(N>=1) G_N t^N = t/(1-2t^2) + t^2/(1-3t^2).

Nevertheless, the generating function for the number `nu(N)` of coefficients
of `P_N` equal to one is not rational. With `alpha = log(2)/log(3)`, the exact
even-subsequence formula is

    nu(2n) = 2^(n - floor((n+1)*alpha)) + (1 if n == 1 else 0).

The article proves this formula by integer interval coverage and a carry-gap
count. It then proves, by **two independent algebraic routes**, that the
result cannot come from a linear recurrence:

- a finite-field argument that reduces an assumed constant-coefficient
  recurrence modulo a prime — elementary, and enough for nonrationality;
- a finite-quotient rigidity theorem — no prime, no invertibility, and it
  yields the strictly stronger conclusion that the counts are not P-recursive.

It also proves a natural boundary **twice**: once by a direct Cesaro
computation on the actual coefficient profile, and once from a general theorem
that `sum_n q^floor(n*theta) t^n` has the natural boundary `|t| = q^(-theta)`
for *every* irrational `theta` in (0,1) and *every* `q > 1`. The two radial
constants are reconciled explicitly rather than left looking contradictory.
Natural boundary gives non-D-finiteness and the absence of
polynomial-coefficient linear recurrences.

The article proves all of this **without assuming anything about the
algebraicity or transcendence of the exponential growth constant**
`2^(1-log_3(2))`. Neither property is needed, and neither is claimed.

## The classified family

For the family with exponents interleaving `a^j` and `q^j` and digit
polynomial `1+y+...+y^(a-1)`, for `2 <= a < q`, the article proves a
**five-way equivalence**: the bases are multiplicatively dependent
(`q^u = a^v`) if and only if the even-section series is rational, if and only
if it is D-finite, if and only if the full series is rational, if and only if
the full series is D-finite.

For `a = 2` — the original binomial factors `1 + x^(G_i)` — multiplicative
dependence reads "`q` is a power of two". So: the count series is rational
exactly when `q` is a power of two, and **for every other `q` it is not even
D-finite**.

The exponents are **not monotone** (`G_6 = 9` is followed by `G_7 = 8`). The
original question requires only positive integers tending to infinity. The
result does not settle a separately imposed monotone variant, a variant
restricted to a single simple dominant characteristic root, or a
classification of all rational exponent generating functions.

## Contents

- `article.pdf` — the complete 32-page article, including all proofs.
- `article.tex` — editable LaTeX source; bibliography is included in the source.
- `short_proof.md` — a compact standalone proof, with both algebraic routes.
- `RESEARCH_STATUS.md` — source attribution, literature-search scope, and limits.
- `code/mixed_base.py` — exact formulas, direct polynomial expansion, an
  independent interval-event sweep, the streaming recurrence, the general
  even/odd identity, and an independent ternary closed form; standard library only.
- `code/verify.py` — the executed finite verification suite and data generator.
- `code/make_figures.py` — optional figure regeneration; requires Matplotlib.
- `data/verification.json` — actual verification results and histogram digest.
- `data/direct_prefix_checks.json` — coefficient-one locations for `P_0` to `P_28`.
- `data/sequence.csv` — `G_N` and `nu(N)`, for indices 0 through 1000.
- `data/even_subsequence.csv` — threshold, count, and power-of-two exponent.
- `data/b_even.txt` — two-column sequence data, without a claimed OEIS identifier.
- `data/base_comparison.csv` — even-prefix counts for eight base pairs,
  `n = 0..100`: the dependent and independent cases side by side.
- `figures/` — the two figures in vector PDF and PNG forms.
- `Makefile` — `make test`, `make quick`, `make pdf`, `make all`, `make clean`.
- `build.py` — cross-platform PDF rebuild helper.
- `environment.txt` — recorded execution and build environment.

## Run the exact verification

From this directory, with Python 3.9 or later:

```text
python code/verify.py
```

or `make all` to verify and then rebuild the PDF.

This command uses **no third-party Python packages**. Do not use `python -O`,
because verification uses assertions. A successful run prints `"status": "PASS"`
and regenerates the data files. A reduced run is available as
`python code/verify.py --quick`; the full run is the one reported in the
article and is the one to prefer. The elapsed time in the verification JSON
will change on a new run.

The supplied run passed 625 direct/sweep/formula rectangle comparisons, 384
larger sweep comparisons, 1,210 independent interval-sweep grid cases, 150
seeded random sweep cases (seed 20260919), 150 gap-distribution checks, 156
wider ruler-identity checks, 29 full prefix checks, 149,050 exact threshold
checks, 10,001 floor-formula checks, 2,001 independent ternary closed-form
checks, 1,000 checks each of the input recurrence and even/odd relation,
18,600 binary-family threshold and quotient checks, 37,262 streaming-recurrence
checks, 37,262 general even/odd identity checks, 1,608 checks for eight base
pairs with `a >= 3`, 4,774 exponent-recurrence checks, 5,409 power-of-two
subfamily checks, and 1,127 dependent-base recurrence checks. The largest
directly expanded polynomial had degree 2,407,867. The whole suite takes about
19 seconds.

Import the implementation directly:

```python
from mixed_base import interleaved_count, count_one, even_count_stream

assert interleaved_count(2, 3, 20) == 16
assert count_one(2, 3, 10, 10) == 16
assert list(even_count_stream(2, 3, 10)) == [1, 2, 2, 2, 2, 4, 4, 4, 8, 8, 16]
```

`even_count_stream` streams the sequence with one exact threshold comparison
per new term. It avoids floating-point logarithms entirely.

## What computation does and does not certify

The dense multiplication and the interval-event sweep are independent of the
closed-form threshold formula; the streaming recurrence is independent of both;
and for the binary/ternary case a fourth routine evaluates the floor formula
through the unrelated comparison `3^s >= 2^(n+1)`. They check implementation
and indexing against each other.

**These are finite consistency checks, not substitutes for the infinite
proofs.** The universal nonrationality, the non-P-recursiveness, the
natural-boundary theorem, and the base classification are consequences of the
written proofs, not of the finite test ranges. Finite tests alone could not
establish those conclusions.

All correctness decisions use exact integers. No floating-point logarithm is
used to decide a threshold or compute an exported sequence term; the article
explains the near-integer hazard that makes this necessary.

To print a prefix of the full sequence:

```text
python code/mixed_base.py 40 --a 2 --q 3
```

## Rebuild the article

The supplied PDF can be read without installing any tools. To rebuild it, use
a LaTeX distribution with pdfLaTeX and the packages named in `article.tex`
(including `newpxtext`, `newpxmath`, and `microtype`). All figures are bundled.

```text
python build.py
```

To verify first and then rebuild:

```text
python build.py --verify
```

The equivalent direct commands are:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

No BibTeX run is needed. Regenerating the figures is optional and additionally
requires Matplotlib:

```text
python code/make_figures.py
```

The figure script uses floating-point numbers only for visualizing normalized
counts. The vector figure PDFs already supplied suffice to rebuild the article.
Font binaries and third-party papers are not redistributed; sources are cited
in the article.

## Source and research status

The target is Richard Stanley's MathOverflow question 431075, posted September
23, 2022. Its page was inspected September 19, 2026. See `RESEARCH_STATUS.md`
for links and the distinction between the proved mathematics and the limited
priority search. This report has not been independently refereed or checked by
a formal proof assistant. No post, submission, or change to an external service
has been made.
