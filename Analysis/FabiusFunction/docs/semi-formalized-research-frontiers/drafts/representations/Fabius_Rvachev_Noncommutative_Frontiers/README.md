# Noncommutative Cumulant Frontiers for the Fabius--Rvachev Law

This package arrived on 2026-08-30 as
`drafts/incoming/Fabius_Rvachev_Noncommutative_Frontiers.zip`, introduced by
repository commit `536c5b42d71e9048b2399f5929fd8fdf7cd34c04`. Its exact outer
SHA-256 is
`55f780d0780a693f2450fe6a4c8a63ba964b3d0e6fcea6d985040c6cb29e25cc`;
the original archive bytes remain recoverable from that commit.

## Main files

- `Fabius_Rvachev_Noncommutative_Frontiers.tex` -- complete LaTeX source.
- `Fabius_Rvachev_Noncommutative_Frontiers.pdf` -- matching rendered report.
- `numerical_experiments.py` -- commented exact/high-precision computations.
- `results/` -- rational certificates, symbolic formulas, CSV tables, Sturm
  data, and numerical diagnostics.
- `figures/` -- retained PDF originals and PNG companions for the generated
  figures.
- `requirements.txt` -- Python dependency constraints.
- `SHA256SUMS` -- exhaustive 21-entry live payload ledger for the normalized
  source, generated evidence, and rebuilt PDF.

## Corpus and formalization boundary

The dyadic probability law, classical moment and cumulant recurrences,
Bernoulli--Bell formulas, Jacobi/continued-fraction representations, finite
sinc products, q-binomial/Richardson machinery, inverse-Fabius and Legendre
transforms, and Lambert-W endpoint analysis are inherited from the repository
corpus. The report's distinct focus is its free- and Boolean-cumulant layer,
the exact non-free-infinite-divisibility certificates, and the resulting
conjectures. It does not claim the inherited interfaces anew, and its novelty
language is relative to the audited corpus rather than a worldwide priority
claim.

Theorem-like labels certify arguments in the paper, not Lean declarations.
At intake, the live Lean tree had no exact counterpart for the free or Boolean
cumulants, the shifted free-cumulant Hankel obstruction, the parameter-uniform
obstruction, or the Jacobi-stripping results. Those remain research-frontier
formalization obligations; only separately cross-referenced inherited inputs
may be described as Lean-backed.

## Reproducing the computations

Create an isolated environment and install the recorded dependency ranges:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install --upgrade pip
.venv/bin/python -m pip install -r requirements.txt
```

Run the three stages as separate Python processes to bound memory during the
largest symbolic Jacobi expansion:

```bash
.venv/bin/python numerical_experiments.py --task jacobi \
  --output-dir results --jacobi-order 8

.venv/bin/python numerical_experiments.py --task finite \
  --output-dir results --finite-order 6

.venv/bin/python numerical_experiments.py --task analysis \
  --output-dir results --figure-dir figures \
  --exact-order 60 --endpoint-order 200 --hankel-max 10
```

The exact stages use Python `Fraction` and SymPy rational/integer arithmetic;
decimals attached to exact certificates are emitted only after exact
calculation, while endpoint and threshold diagnostics use the stated
high-precision arithmetic. The four generated CSV files use deterministic LF
line endings. The plotting stage retains both vector PDF and PNG output. It
uses the headless Agg backend, embeds plot text as TrueType rather than Type 3
glyphs, and omits volatile PDF date metadata; repeated runs in the recorded
environment produce byte-identical vector files. The report continues to
embed the byte-identical PNG twins.

## Compiling the report

The arrival PDF was a 29-page US-Letter rendering whose included vector plots
introduced Type 3 fonts. The normalized source uses A4 paper, 27 mm margins,
the repository palette and running heads, and conditional Libertinus prose;
the regenerated standalone vector plots now contain only embedded, subset
CID TrueType fonts.
After every source change, run exactly three serial passes from this directory:

```bash
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Noncommutative_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Noncommutative_Frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Noncommutative_Frontiers.tex
```

Use a TeX installation with the Libertinus Type 1 package. Before refreshing
the ledger, verify A4 geometry, a positive Libertinus font count, embedded and
subset fonts, no Type 3 fonts, no unresolved references or rerun request, and
no overfull boxes. Remove only TeX sidecars such as `.aux`, `.log`, `.out`, and
`.toc`; the files under `results/` are reproducibility payloads.

## Current validation receipt

The current source was rebuilt on 2026-08-31 from a clean auxiliary state in
exactly three strict serial `pdflatex` passes, which produced 25, 26, and 26
pages. The final PDF is 723,151 bytes with SHA-256
`397caa036acbc4a7b72cad881da236693e9261a3ca0dde677f6fee91e9d13c68`;
the 1,318-line, 64,984-byte source has SHA-256
`5b9088e4a9b2a70f19b7849b4c7183fb97b6472c4b964a9d4d5be78133d0bfd7`.

All 26 pages are A4 with zero rotation and nonblank extractable text. The PDF
has complete title, author, subject, and keyword metadata. All 19 font rows
are embedded and subset, four are Libertinus, and none is Type 3. The report
embeds the retained PNG twins on pages 11 and 18. The final log has no
LaTeX/package warning, overfull or underfull box, TeX error, unresolved
reference/citation, duplicate destination, or rerun request. Pages 1, 11, 18,
and 26 were inspected at full-page resolution and are unclipped and readable.
All 21 live payload checksums verify after the synchronized source, PDF,
README, and ledger refresh. The three retained one-page vector plot PDFs also
have all fonts embedded and subset and contain no Type 3 fonts.
