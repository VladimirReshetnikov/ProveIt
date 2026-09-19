# Sharp discrepancy for a family of binary substitutions

Research article and reproducible exact computations, September 19, 2026.
Prepared with ChatGPT.

## Result

For the fixed word of `0 -> 1, 1 -> 101010`, the OEIS position sequences
A284365 (zeros) and A284366 (ones) conjecture upper position errors below 2.
Both are false. The first counterexamples are:

| Sequence | Rank n | Position a(n) |
| --- | ---: | ---: |
| A284366, positions of 1 | 2,977,771 | 5,334,043 |
| A284365, positions of 0 | 8,933,313 | 20,222,898 |

The common error is `(2977771*sqrt(21)-13645857)/2`, approximately
2.00487217332612884794. The sharp common upper bound is
`(6+sqrt(21))/5`, approximately 2.11651513899116800132.

The article proves complete discrepancy limit intervals for every substitution
`0 -> 1, 1 -> (10)^m`, m >= 1. It also proves the density statements,
constructs infinite counterexample families, and derives exact recurrences
and rational generating functions for their indices.

## Read the article

- `article.pdf`: 17-page compiled article (page count may shift with TeX versions).
- `article.tex`: complete LaTeX source with embedded bibliography.

The source OEIS entries were still labeled conjectural when accessed on
September 19, 2026. This manuscript supplies self-contained mathematical
proofs and executed exact certificates. It is not peer reviewed or
proof-assistant formalized, and an exhaustive literature/priority check has
not been performed. Classical substitution-discrepancy methods are not
claimed as new. The exact assertions and certificates can be checked
independently of any novelty claim.

## Run the verification

Requires Python 3.10 or later; all verification code uses only the standard
library. Run these commands from this directory:

```sh
python code/independent_check.py
python code/verify.py --long
```

The long test literally generates a prefix of 20,222,898 binary letters.
The main algorithm does not need to allocate this word; the literal build
is an independent cross-check. A memory-lighter run is:

```sh
python code/verify.py
```

A successful verification writes `data/verification.json` and regenerates the
certificate and sequence data. The delivered report records a successful
`--long` run with 310,816 counted checks, plus assertions within the independent
checker. Running without `--long` overwrites the report with one that records
that the optional large-word test was omitted.

All decisions about inequalities, extrema, and first violations use exact
integer arithmetic in the quadratic field. Decimal arithmetic is used only
for displaying values and a secondary small-coefficient arithmetic cross-check.
The interval theorem is proved in the article, not inferred from these tests.

## Files

- `code/substitution.py`: typed exact arithmetic and recursive word tools.
- `code/independent_check.py`: separate compact certificate checker; it does not
  import the main library.
- `code/verify.py`: tests, first-counterexample search, and data generation.
- `code/make_figure.py`: regenerates the illustration; requires Matplotlib.
- `data/certificates.json`: exact first-violation descent traces, prefix counts,
  minimum coefficients, and integer square certificates.
- `data/finite_extrema.json`: exact block extrema for W_0 through W_30.
- `data/extremal_family.json`: first 25 terms of the constructive extremal family.
- `data/verification.json`: executed test report.
- `figures/finite_maxima.pdf` and `.png`: vector/raster illustration.
- `oeis_proposed_updates.txt`: suggested corrections; not submitted to OEIS.

Quadratic values in JSON are encoded as `{"m": m, "a": a, "b": b}` for
`a + b*q`, where `q = (sqrt(m*m+4*m)-m)/2`. Ranks and letter positions are
1-based. Prefix lengths and internal extremum offsets are 0-based.

## API example

Run from `code/`, or add `code/` to `PYTHONPATH`:

```python
from substitution import Substitution

model = Substitution(3)
print(model.select(1, 2977771))       # 5334043
print(model.select(0, 8933313))       # 20222898
print(model.prefix_counts(5334042))  # (2356272, 2977770)
print(model.first_at_least(1, threshold=2))
```

`first_at_least` returns the earliest error >= the given integer threshold
through the searched block range. Its `None` result means no witness was
found up to `max_level` (default 128), not a proof that none exists in the
infinite word. The implementation's complexity discussion assumes fixed m;
integer bit costs are accounted for separately in the article.

## Build the PDF

The pre-rendered figure is included. A conventional TeX installation with
`newpxtext`, `newpxmath`, `amsmath`, `amsthm`, `mathtools`, `microtype`,
`tcolorbox`, `listings`, `hyperref`, and the other packages named in the
preamble is sufficient:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The `Makefile` provides `pdf`, `verify`, `figure`, and `clean` targets.
To regenerate the plot independently:

```sh
python code/make_figure.py
```

## Verification boundaries

The first 30 displayed terms of each position sequence and the first 30
binary letters were compared to OEIS. The complete linked 10,000-term b-files
were not downloaded or compared. The independently generated large prefix
and exact first-violation search are separate from those OEIS spot checks.

The exact optimal factor-balance constant, the distribution of errors inside
their interval, and the density of violating ranks are not determined here.
Sharp prefix intervals alone do not answer these stronger questions.

## Primary references

- https://oeis.org/A284364
- https://oeis.org/A284365
- https://oeis.org/A284366
- B. Adamczewski, *Symbolic discrepancy and self-similar dynamics*, Annales de
  l'Institut Fourier 54 (2004), no. 7, 2201–2234, doi:10.5802/aif.2079.
  https://www.numdam.org/item/AIF_2004__54_7_2201_0/

No external papers, fonts, checksum files, or transient TeX build files are
bundled. No OEIS changes have been submitted.
