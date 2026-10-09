# Polylogarithms and their Arithmetic Bridges

The unified reading manuscript is [polylogarithms.pdf](polylogarithms.pdf),
built from [polylogarithms.tex](polylogarithms.tex) and its edited chapter
sources. It integrates all 39 textual source documents into ten chapters and
a literature appendix. The chapters follow mathematical dependency:
foundations, cyclotomic coordinates, algebraic arguments and ladders, depth,
gamma certificates, CM lattices, integrated zeta jets, differentiated zeta
jets, Herglotz arithmetic, and experimental discovery.

The [editorial ledger](EDITORIAL-LEDGER.md) maps every source to its retained
material and explains the corrections. The [source inventory](source-inventory.json)
records SHA-256 digests. Original drafts and old PDFs remain historical
evidence; the unified manuscript supersedes them as a reading artifact.

The work combines proved analytic identities, exact finite computations
relative to specified laws, numerical candidate identities, and bounded
negative searches. These statuses are distinguished in the manuscript.
There is no proof-assistant formalization. In particular, numerical
independence, minimal depth, gamma completeness beyond the standard relations,
and the Stark regulator candidates are not claimed as unconditional theorems.

## Reproduction

Run from this directory, with LuaLaTeX, Python with mpmath, and Wolfram Language
available:

```powershell
python verification/check_document.py
python verification/check_identities.py
wolfram -script verification/check-identities.wls
lualatex -interaction=nonstopmode -halt-on-error polylogarithms.tex
lualatex -interaction=nonstopmode -halt-on-error polylogarithms.tex
lualatex -interaction=nonstopmode -halt-on-error polylogarithms.tex
```

Numerical receipts in `verification/` are fresh focused checks of the
corrected and retained formulas, with engine, precision, tolerances and
individual residuals. They are separate from historical Smithereens search
receipts quoted in the text. The historical tools and stores were not all
imported; their absence is documented rather than presented as a replay.

The [validation report](VALIDATION.md) records the completed source audit,
31 native Wolfram checks, 67 independent mpmath checks, converged 100-page
PDF and visual review. It pins the artifact by SHA-256 and distinguishes
these checks from unproved numerical identities and historical receipts.
