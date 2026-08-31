# Dyadic-Comb Frontiers for the Fabius–Rvachev System

> **Source-only merge status (2026-08-31).** The current root TeX has 5,648
> lines (SHA-256
> `8fa52a142c14ea77cdc916f9fca8034b68718fc076d62a064f38af92c3fd4d6a`).
> The retained 66-page PDF was not rebuilt after the notation migration and is
> not claimed to be synchronized with that source. This volume has no live
> checksum ledger covering the root TeX/PDF pair; historical build statements
> below describe the preceding checkpoint.

One editorially merged volume (2026-08-28) consolidating the six
dyadic-comb drafts of the second and third waves:

- **Part I — Comb sums and quadrature**, merged from
  - `Fabius_Dyadic_Comb_Sums_Report_Package/` (*Dyadic-Comb Sums for the
    Fabius–Rvachev System*),
  - `fabius-dyadic-comb-sums-report/` (*Dyadic-Comb Moments of the Fabius
    and Rvachev Functions*),
  - `fabius_dyadic_comb_report_final/` (*Dyadic-Comb Quadrature for the
    Fabius and Rvachev Functions*);
- **Part II — Global polynomial interpolation**, merged from
  - `fabius_dyadic_interpolation_report/` (*Dyadic-Comb Interpolation of
    the Fabius and Rvachev Functions*),
  - `fabius_interpolation_report/` (independent write-up with the same
    title),
  - `Fabius_Rvachev_Dyadic_Interpolation_Report/` (*Global Polynomial
    Interpolation of the Fabius and Rvachev Functions on Dyadic Combs*).

Unlike the mechanical part-per-source consolidations elsewhere in this
corpus, the six sources largely re-derive one another's core results,
so this volume is a true merge: one unified notation (level `m`,
`M = 2^m`), each shared theorem stated once with the clearest available
proof (alternative arguments kept as remarks), and all source-specific
tables, experiments, conjectures, and programs retained.  Two exact
spectral Dirichlet values new to this volume, `D(6)` and `D(8)`, were
computed for the merge and cross-validated; the method is described
where they appear (Part I, "The first defect and spectral Dirichlet
values").

Provenance of the absorbed sources — directory names, SHA-256 of each
main `.tex` at absorption, what each contributed, and what was
deduplicated — is Appendix E of the volume.  Every supporting file of
every source (experiment scripts, CSV data, generated tables, figures,
READMEs, per-source SHA manifests) is preserved verbatim under
[`assets/`](assets/); the volume's figures are included from there.
The absorbed draft directories are deleted; git history is the archive.

## Build

```bash
pdflatex -interaction=nonstopmode Dyadic_Comb_Frontiers.tex
pdflatex -interaction=nonstopmode Dyadic_Comb_Frontiers.tex
```

(Two passes; `latexmk -pdf` also works.  Figures resolve via
`\graphicspath` into `assets/`.)

## Reproduce the numerics

Each source package under `assets/` is self-contained with its own
README and entry-point script (exact `fractions.Fraction` arithmetic
for every exact claim; `mpmath` for high-precision scans).  See the
volume's verification sections (Part I §11, Part II §18) for what each
suite checks.
