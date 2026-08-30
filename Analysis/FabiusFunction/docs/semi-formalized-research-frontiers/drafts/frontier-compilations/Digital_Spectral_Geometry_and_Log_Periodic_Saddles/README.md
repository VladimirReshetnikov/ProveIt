# Digital spectral geometry and log-periodic saddles

This directory contains a manuscript-level frontier report and its numerical
diagnostics. A theorem label means that the TeX manuscript supplies a proof;
it does not assert an exact Lean formalization. The numerical outputs are
consistency checks, not proofs.

## Maintained source and generated outputs

- `Fabius_Rvachev_Frontier_Report.tex` is the report source.
- `numerical_experiments.py` generates the numerical tables, summary, and
  three figures.
- `requirements.txt` pins the two top-level Python dependencies from the
  successful captured run.
- `numerical_results.tex`, `numerical_summary.txt`,
  `psi_coefficients.png`, `psi_periodic.png`, and
  `zero_count_digit_sum.png` are generated outputs.
- `numerical_run.txt` records the successful command, resolved environment,
  and generated-output hashes.
- `repository_audit.md` records the bounded current-corpus audit and the
  paper-versus-Lean boundary.
- `SHA256SUMS` is the exhaustive 17-entry ledger for the normalized live
  package; `ARRIVAL_SHA256SUMS` preserves the received ten-member ledger.

Python 3.10 or newer is required by the script syntax. The captured successful
environment used Python 3.13.14, `mpmath==1.4.1`, and
`matplotlib==3.11.1`. Both Python packages are required to regenerate the
complete checked-in output set, including all three figures.

From this directory, the exact successful generation command was:

```bash
uv run --with mpmath --with matplotlib python numerical_experiments.py --output-dir .
```

After the generated inputs exist, build the report with exactly three passes:

```bash
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Frontier_Report.tex
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Frontier_Report.tex
pdflatex -interaction=nonstopmode -halt-on-error Fabius_Rvachev_Frontier_Report.tex
```

The TeX dependency set is declared in the canonical report preamble. A
compliant build should make Libertinus available; the source retains the
repository-standard Latin Modern fallback.

The normalized source is 1,938 lines and the repaired generator is 488 lines.
The final three-pass artifact is 24 A4 pages; every font is embedded and
subset, Libertinus is present, Type 3 fonts are absent, and the final log has
no overfull box, error, unresolved-reference, or rerun warning. All 17 entries
in `SHA256SUMS` verify against the live files.

## Arrival provenance

`compile_transcript.txt`, `pdf_validation.txt`, `delivery_manifest.txt`, and
`numerical_generation_error.txt` are records from the received bundle. They
do not certify the repaired source, rebuilt PDF, or regenerated numerical
outputs. The received PDF remains recoverable from the recorded intake commit.
`ARRIVAL_SHA256SUMS` is the immutable ledger for that arrival state and is not
to be refreshed after repair. Current live-file hashes belong in the
repository's separate live ledger.
