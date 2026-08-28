# Euler--Maclaurin and Exhaustion Quadratures for Fabius and Rvachev Moments

This package contains the complete LaTeX research report, the rendered PDF,
and reproducible exact-arithmetic experiments requested for the study of
Euler--Maclaurin/Ruffa summation applied to polynomially weighted Fabius and
Rvachev integrals.

## Main files

- `fabius_euler_maclaurin_report.pdf` — rendered 20-page report.
- `fabius_euler_maclaurin_report.tex` — complete LaTeX source.
- `fabius_em_experiments.py` — documented Python experiment and table generator.
- `data/` — exact CSV outputs, generated LaTeX tables, numerical audit log,
  and the termination figure in PDF/PNG form.
- `SOURCE_AUDIT.md` — source and nonduplication notes.
- `Makefile` — reproducible experiment and PDF build targets.
- `SHA256SUMS` — checksums for every packaged file except the checksum file itself.

## Reproduce the calculations

Python 3.11 or newer is recommended. The exact computations use only the
standard library. Matplotlib is optional and is used solely to regenerate the
figure.

```bash
python3 fabius_em_experiments.py \
  --output-dir data \
  --max-power 10 \
  --max-level 10
```

All theorem-level exactness tests use `fractions.Fraction` and assertions. A
failed identity causes the script to stop rather than silently round a value.

## Rebuild the report

A reasonably complete TeX Live installation with `latexmk` is sufficient.

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  fabius_euler_maclaurin_report.tex
```

Or run:

```bash
make all
```

The source uses the generated files under `data/`, so keep that directory next
to the main `.tex` file.

## Scope of novelty

“New” in the report means new relative to the inspected ProveIt
Fabius-function corpus and the cited summation sources. The report explicitly
retains known Fabius moment formulas and the existing dyadic shifted
self-sampling theorem for Rvachev's up-function as prior art. No claim of
universal publication priority is made.
