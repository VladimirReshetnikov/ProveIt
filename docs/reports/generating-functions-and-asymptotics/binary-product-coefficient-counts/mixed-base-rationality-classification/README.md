# A mixed-base counterexample to Stanley's rationality question

This package contains an 18-page article with self-contained proofs, editable
LaTeX source, exact-integer Python code, verification results, and sequence data.

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
count. It proves nonrationality by a finite-field argument, and then proves
a natural boundary, non-D-finiteness, and non-P-recursiveness.

It also classifies rationality within the family with exponents interleaving
`a^j` and `q^j` and digit polynomial `1+y+...+y^(a-1)`, for `2 <= a < q`:
the coefficient-one generating function is rational exactly when `q^u = a^v`
for some positive integers `u,v`.

The exponents are **not monotone**. The original question requires only
positive integers tending to infinity. The result does not settle a separately
imposed monotone variant or classify all rational exponent generating functions.

## Contents

- `article.pdf` — the complete article, including exact formulas and all proofs.
- `article.tex` — editable LaTeX source; bibliography is included in the source.
- `short_proof.md` — a compact standalone proof of the counterexample.
- `RESEARCH_STATUS.md` — source attribution, literature-search scope, and limits.
- `code/mixed_base.py` — exact formulas, direct polynomial expansion, and an
  independent interval-event sweep; Python standard library only.
- `code/verify.py` — the executed finite verification suite and data generator.
- `code/make_figures.py` — optional figure regeneration; requires Matplotlib.
- `data/verification.json` — actual verification results and histogram digest.
- `data/direct_prefix_checks.json` — coefficient-one locations for `P_0` to `P_24`.
- `data/sequence.csv` — `G_N` and `nu(N)`, for indices 0 through 1000.
- `data/even_subsequence.csv` — threshold, count, and power-of-two exponent.
- `data/b_even.txt` — two-column sequence data, without a claimed OEIS identifier.
- `figures/` — the two figures in vector PDF and PNG forms.
- `build.py` — cross-platform PDF rebuild helper.
- `environment.txt` — recorded execution and build environment.
- `SHA256SUMS.txt` — checksums of the packaged files, excluding the checksum file.

## Run the exact verification

From this directory, with Python 3.9 or later:

```text
python code/verify.py
```

This command uses **no third-party Python packages**. Do not use `python -O`,
because verification uses assertions. A successful run prints `"status": "PASS"`
and regenerates the data files. The elapsed time in the verification JSON will
change on a new run, so its packaged checksum will then change too.

The supplied run passed 625 direct/sweep/formula rectangle comparisons, 384
larger sweep comparisons, 150 gap-distribution checks, 25 full prefix checks,
149,050 exact threshold checks, 10,001 floor-formula checks, 1,000 checks each of
the input recurrence and even/odd relation, and 1,127 dependent-base recurrence
checks. The largest directly expanded polynomial had degree 269,815.

**These are finite consistency checks, not substitutes for the infinite proofs.**
All correctness decisions use exact integers. No floating-point logarithm is
used to decide a threshold or compute an exported sequence term.

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

## Source and research status

The target is Richard Stanley's MathOverflow question 431075, posted September
23, 2022. Its page was inspected September 19, 2026. See `RESEARCH_STATUS.md`
for links and the distinction between the proved mathematics and the limited
priority search. This report has not been independently refereed or checked by
a formal proof assistant. No post, submission, or change to an external service
has been made.
