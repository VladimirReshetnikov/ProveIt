# Round 23 native report

The complete report is `ConZFC_Joint_Pell_Certificates_Round23_2026-10-26.pdf`.
`main.tex` and the 30 other native inputs listed in `TEX_SOURCE_CLOSURE.json`
are its editable source. No imported PDF pages or screenshots are used as
mathematical content.

## Build

From the combined release root:

```sh
sh report/build_report.sh
python3 report/check_source_closure.py
```

The build runs native pdfLaTeX three times in a fresh temporary directory. It
requires a POSIX shell, `mktemp`, `cp`, `grep`, `kpsewhich`, `pdftex`, `pdflatex`,
and a TeX Live installation providing the packages named in `main.tex` (including
Latin Modern, AMS mathematics, mathtools, booktabs, longtable, microtype, enumitem,
fvextra, xurl, hyperref and bookmark). A local format is constructed if the
installed `pdflatex.fmt` is unavailable. Python checks use Python 3's standard
library. No network, proof assistant, source search, or optimization is needed
to build the supplied native report.

The optional first argument to `build_report.sh` is an output PDF path. Build
logs are written under `report/qa/compile_logs/`; rebuilding may change those
logs and PDF metadata on a different TeX distribution. The delivered PDF's
binding and author visual review are in `REPORT_QA.json`.

## Check the complete printed residuals

```sh
python3 report/check_printed_residuals.py \
  --equation signed/principal210/equation.json --tex report/residuals.tex
python3 report/check_printed_residuals.py \
  --equation signed/conservative209/equation.json \
  --tex report/conservative_residuals.tex
```

These parse every printed coefficient independently, without importing a
producer. The principal and conservative coordinate namespaces are separate.
Appendix C gives the exact ports, retained-norm corrections, seed definitions
and all 249 ordered unit-pivot entries for the three selected reciprocal
polynomials. The normative pivot polynomials and retained-index lists are in
`reciprocal/equations/*/NATIVE_DEFINITION.json`.

The generation scripts are retained for reproducibility. Run
`python3 report/generate_comparison.py` to regenerate the comparison table from
`audit/INPUT_COMPARISON.json`, or use
`python3 report/render_reciprocal_ledger.py --package reciprocal` to regenerate
the native reciprocal ledger. Both overwrite the corresponding TeX file;
their source hashes must still match the supplied binding receipts before
they are treated as the reviewed document. `render_residuals.py --help` gives
the options for exact residual transcription.

## Evidence and scope

`REPORT_QA.json` records the final three-pass build, complete 80-page author
visual inspection, and independent review references. The render inventory is
included as a receipt, not as replacement source content. Render PNGs, contact
sheets, temporary formats, unused inherited source fragments, and preview
builds are deliberately excluded by `RELEASE_WHITELIST.json`.

The manuscript distinguishes unrestricted integers, nonnegative integers and
strictly positive integers; exact measured support and height from unexpanded
circuit data; new results from inherited controls; and ordinary unbounded
proofs from finite artifact checks. Its calibration is an equivalence with
syntactic ZFC consistency, not a proof of consistency or a new complete
proof-assistant derivation.
