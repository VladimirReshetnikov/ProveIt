# A sharp order-five threshold for higher-order Stirling subset log-concavity

Research report prepared for Vladimir Reshetnikov, 19 September 2026.

## Mathematical result

Let S^(r)_(n,k) be the number of partitions of n+(r-1)k labels into k
blocks, each of size at least r. All rows are log-concave **if and only if
1 <= r <= 5**, with strict inequalities in the interior of the positive
support. This proves the log-concavity assertion of Deb–Sokal,
Conjecture 1.4(c), as stated in arXiv:2507.18959v1.

The article also proves the cycle-number cases r=3,4, an explicit lower
bound for fifth-order subset Turan differences, and an interpolating
recurrence theorem. The fifth-order **cycle** conjecture is not resolved.
Its row operator does not preserve every log-concave input; the included
operator counterexample is NOT a counterexample to the actual conjecture.

The article contains complete ordinary mathematical proofs. It has not
undergone independent peer review or proof-assistant verification.
A targeted literature search did not find a later resolution of the
selected assertion; this is not a guarantee of novelty or priority.

## Files

- `article.pdf`: the complete 18-page research article.
- `article.tex`: standalone LaTeX source, with its bibliography inline.
- `verify.py`: exact integer recurrence tests and independent generating-function checks.
- `certificates.py`: exact rational polynomial verification, without a CAS dependency.
- `data/verification.json`: the recorded default finite run and exact counterexamples.
- `data/certificates.json`: identities and positive shifted coefficients.
- `data/small_rows.csv`: both kinds, r=1,...,8, n=0,...,12, including k=0.
- `data/row_sums.csv`: both kinds, r=1,...,8, n=0,...,30.
- `SOURCES.md`: source locations, statement mapping, and literature-check limitations.
- `PROOF_CHECKLIST.md`: concise checklist for independently auditing the proof.
- `build.py`: optional portable verification-and-PDF build command.

## Run the verification

Python 3.9 or later is sufficient. Only the standard library is used.
Run from the extracted archive directory:

```text
python certificates.py
python verify.py
```

The distributed run checked 45 polynomial identities/positivity certificates,
24 leading-coefficient identities, 197,010 strict integer inequalities,
19,701 quantitative fifth-order subset bounds, and 1,456 entries computed
independently from rational generating functions. All checks passed.
The finite array tests audit the implementation; they are not the all-n proof.

A longer finite regression run is optional:

```text
python verify.py --max-n 500
```

The output includes fifth-order cycle tests, which remain experimental.
Deb–Sokal already reported testing their conjectural cases through row 1000;
our smaller independent run is not a claim to extend that range.

## Build the PDF

A TeX distribution with pdfLaTeX and the packages named in `article.tex`
is needed. No font files are bundled. The fonts are TeX Gyre Pagella and
matching mathematics via `newpxtext` and `newpxmath`.

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, compile twice with pdfLaTeX:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or run both exact verifiers and the build through the portable helper:

```text
python build.py
```

The scripts do not make network requests. The article's references contain
links for manually consulting the primary sources.
