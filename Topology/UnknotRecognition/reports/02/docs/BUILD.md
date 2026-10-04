# Rebuilding the report

A LaTeX installation with `pdflatex`, `lmodern`, `microtype`, `amsmath`,
`amsthm`, `booktabs`, `longtable`, `xurl`, `hyperref`, and `listings` is needed
only to rebuild the report, not to run any Python code.

From this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error implementation_report.tex
pdflatex -interaction=nonstopmode -halt-on-error implementation_report.tex
```

The supplied PDF was built successfully and all ten pages were rendered and
visually inspected. It contains the same status limitation as the README.
