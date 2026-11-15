# Report source and compilation

`report.pdf` is the compiled report. `report.tex` is the main source; all
included `.tex` files are in this directory. The report contains the full
194-state transition tables, not only links to the machine-readable files.

With a standard TeX Live installation providing pdfLaTeX and the packages
named in the preamble:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

An additional pass may be needed if the table of contents changes length.
`generate_tables.py` regenerates the numeric tables and complete transition
appendix directly from the delivered construction and independent receipts:

```sh
python3 generate_tables.py
```

The proof section `gd_calibration.tex` is specific to the ten-entry,
three-operand GD interface. The separately inherited AX11H proof sources
are under `../references/AX11H_written_sources/`, with their own README and
provenance; they are not silently substituted for the new command proof.

The report records a written mathematical equivalence, explicit inherited
dependencies, and independent executable evidence. It does not claim a
completed end-to-end Lean theorem, a 193-state machine, or a lower bound.
