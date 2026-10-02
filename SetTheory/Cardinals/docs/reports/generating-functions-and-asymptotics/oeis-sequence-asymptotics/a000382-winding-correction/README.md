# Winding sectors and the four-displacement restricted-permutation problem

This research draft studies

\[
\Phi_n=\#\{\sigma\in S(\mathbb Z/n\mathbb Z):
\sigma(i)-i\pmod n\in\{0,1,2,3\}\},\qquad n\ge4.
\]

It proves directly that

\[
\Phi_n=2\bigl(A001644(n)+1\bigr),
\]

using a winding-number decomposition and a bijection between the winding-one
sector and cyclic tilings by pieces of lengths 1, 2, and 3. It then diagnoses
the mismatch among OEIS A000382, A000496, A004306, and A008305; derives the
exact correction kernel; and gives exact asymptotics and an inverse
log-periodic transseries.

## Files

- `article.tex` — complete LaTeX source.
- `article.pdf` — compiled report.
- `verify.py` — independent exact subset-DP permanent computation and checks.
- `verification_output.txt` — captured output from the verifier.
- `oeis_corrections.txt` — proposed editable OEIS notes; not submitted.
- `Makefile` — convenience build targets.

## Verification

```bash
python3 verify.py
```

The verifier uses only the Python standard library and checks exact winding
sector counts through `n=16`, all recurrences and generating-function
numerators, the correction kernel, and the nearest-integer formula through
`n=100`.

## PDF build

In the OpenAI artifact environment:

```bash
python /home/oai/skills/pdfs/scripts/latex_to_pdf.py article.tex -o article.pdf
```

A conventional local build also works:

```bash
pdflatex -interaction=nonstopmode article.tex
pdflatex -interaction=nonstopmode article.tex
```

## Suggested repository location

`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a000382-winding-correction/`

This is a research draft. The mathematical proof and historical attribution
should be independently reviewed before an OEIS or journal submission.
