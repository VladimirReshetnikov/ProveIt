# A sharp order-five threshold for higher-order Stirling subset log-concavity

Merged research report prepared for Vladimir Reshetnikov, 19–20 September 2026.
This package merges two independently produced drafts of the same theorem; see
"Provenance" below and Section 1.2 of the article.

## Mathematical result

Let S^(r)_(n,k) be the number of partitions of n+(r-1)k labels into k
blocks, each of size at least r. All rows are log-concave **if and only if
1 <= r <= 5**, with strict inequalities at every internal index (n >= 2,
1 <= k <= n-1). This proves the log-concavity assertion of Deb–Sokal,
Conjecture 1.4(c), as stated in arXiv:2507.18959v1, and nothing else of
that conjecture.

The decisive fifth-order step is the exact identity (4.12),

    25(A_4 u^2 + H_4 uv + v^2)
      = (5v - 8*alpha(t)*u)^2 + 96(t-5)*beta(t)*gamma(t)*u^2
        + 480*beta(t)*(t-5k)*uv,

whose three summands are nonnegative exactly on the triangular domain
t >= 5k >= 10. Equation (4.18) writes the whole interior induction step as
six nonnegative terms in one display.

The article also proves the cycle-number cases r=3,4 (Deb–Sokal 1.3(c) and
BCC30 Problem 30.9 for those orders), an explicit lower bound for fifth-order
subset Turan differences, an interpolating recurrence theorem, and an
asymptotic explanation of why the cutoff sits between orders five and six.
The fifth-order **cycle** conjecture is not resolved. Its row operator does
not preserve every log-concave input; the included operator counterexample is
NOT a counterexample to the actual conjecture.

The article contains complete ordinary mathematical proofs. It is an
unrefereed research manuscript: it has not undergone independent peer review
or proof-assistant verification. A targeted literature search did not find a
later resolution of the selected assertion; this is not a guarantee of
novelty or priority.

## Files

- `article.pdf`: the complete 25-page research article.
- `article.tex`: standalone LaTeX source, with its bibliography inline.
- `certificates.py`: exact rational polynomial verification, **without** a CAS
  dependency (51 identities/positivity certificates, 24 leading-coefficient checks).
- `verify.py`: exact integer recurrence tests for ten triangles through n=200,
  plus independent generating-function entry checks.
- `code/verify_certificates.py`: the same polynomial identities under SymPy
  (24 named checks), including the bivariate identity (4.12) in one piece.
- `code/verify_rows.py`: standard-library subset scan through n=300, the full
  six-term certificate at 1711 indices, and block-profile entry counts.
- `data/certificates.json`: CAS-free identities and positive shifted coefficients.
- `data/certificate_checks.json`: the SymPy check report, with versions used.
- `data/verification.json`: the ten-triangle run, counterexamples for r=6..12,
  and the machine-readable cycle-operator obstruction record.
- `data/row_checks.json`: the n<=300 subset run, counterexamples for r=6..20
  with full triples and defects, and largest-entry bit lengths.
- `data/row_checks.txt`: a compact summary of that run.
- `data/small_rows.csv`: both kinds, r=1,...,8, n=0,...,12, including k=0.
- `data/row_sums.csv`: both kinds, r=1,...,8, n=0,...,30.
- `data/sample_rows.json`: subset rows n=0..8 for r=1..8, in JSON form.
- `SOURCES.md`: source locations, statement mapping, attribution, and the
  limitations of the literature check.
- `PROOF_CHECKLIST.md`: checklist for independently auditing the proof.
- `build.py`, `Makefile`, `requirements.txt`: reproducibility helpers.

There is no checksum manifest in this package, and none should be added.

## Run the verification

Three of the four checkers need only the Python standard library
(`certificates.py` and `verify.py` run on Python 3.9+; `code/verify_rows.py`
uses Python 3.10 syntax). Run from this directory:

```text
python certificates.py
python verify.py
python code/verify_rows.py --max-n 300 --output-dir data
```

The SymPy checker is the only component with a third-party dependency:

```text
python -m pip install -r requirements.txt
python code/verify_certificates.py --output data/certificate_checks.json
```

The recorded run here used Python 3.14.4 with SymPy 1.14.0; the second source
draft recorded SymPy 1.14.0 under Python 3.13.5. `make check`, `make pdf` and
`make clean` are available, as is `python build.py` (which skips the SymPy
step with a notice if SymPy is absent).

The distributed run checked 51 CAS-free polynomial identities/positivity
certificates, 24 leading-coefficient identities, 24 SymPy identities,
197,010 strict integer inequalities across ten triangles, 224,250 strict
inequalities across the five subset triangles through n=300, 19,701
quantitative fifth-order bounds, 1,456 entries computed independently from
rational generating functions, 728 entries computed independently from
block-size profiles, 1,711 full six-term certificate evaluations, the
third-row closed form for r=1..100, and first failures for r=6..20.
All checks passed. The finite array tests audit the implementations; they
are not the all-n proof.

A longer finite regression run is optional:

```text
python verify.py --max-n 500
```

The output includes fifth-order cycle tests, which remain experimental.
Deb–Sokal already reported testing their conjectural cases through row 1000;
neither of our runs is a claim to extend that range.

## Why two of almost everything

The merge deliberately keeps twelve duplications — two certificate forms, two
routes to the mixed-coefficient bound, two derivations of the order-six
counterexample entries, two entry-verification routes, two toolchains, two
scan ranges, and so on. Appendix B of the article lists all twelve with one
sentence each on what the duplication buys. Collapsing any of them would
remove an independent check.

## Build the PDF

A TeX distribution with pdfLaTeX and the packages named in `article.tex`
is needed. No font files are bundled; the fonts are TeX Gyre Pagella and
matching mathematics via `newpxtext` and `newpxmath`, which must be present
in the distribution. There is no external bibliography processor, image
asset, or shell-escape step.

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The supplied PDF compiles with no overfull or underfull boxes and no LaTeX
or pdfTeX warnings.

Alternatively, compile three times with pdfLaTeX:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The scripts do not make network requests. The article's references contain
links for manually consulting the primary sources.

## Provenance

This package is the merge of two research packages that proved the same
theorem independently:

- `docs/reports/log-concavity-and-unimodality/higher-order-stirling-rows`
  (19 September 2026), which bounded the mixed coefficient by convexity of the
  falling factorial and completed the square against a factored discriminant,
  and which additionally proved the cycle cases r=1..4, the interpolating
  family, and the asymptotics;
- `docs/reports/log-concavity-and-unimodality/stirling-subset-cutoff`
  (20 September 2026, recorded there as drafted with ChatGPT), which replaced
  that detour by the exact identity H_4 - L_4 = (96/5)*beta(t)*(t-5k) and
  packaged the whole interior step as one sum of nonnegative terms.

The first package is the spine and supplies the notation; the second supplies
the primary fifth-order certificate. Both packages' code and data are kept.
