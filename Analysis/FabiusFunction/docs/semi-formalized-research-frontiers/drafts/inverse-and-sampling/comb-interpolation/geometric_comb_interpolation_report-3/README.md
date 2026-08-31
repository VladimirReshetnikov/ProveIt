# Interpolation on a geometric comb: archival intake

> **Source-only merge status (2026-08-31).** The current TeX has 2,735 lines
> (SHA-256
> `df9456de278b3608658797ffaedf415526e487e1124a86e0907ca00c6b1cc349`).
> The retained submitted 36-page PDF was not rebuilt after the notation
> migration and is not claimed to be synchronized with that source.
> `SHA256SUMS.txt` was intentionally not refreshed: its TeX row, this README
> row, and the relocated intake-audit row are pending, while its other
> twenty-two rows pass.

This collision-safe package contains the distinct report titled
*Interpolation on a Geometric Comb: Lagrange Filters, Jackson--Newton Series,
$q$-Analogues, and the Fabius--Rvachev Bridge*.

## Intake status

This package has passed only the quick archival intake gate. The archive was
tested for path safety and payload integrity, its submitted checksum ledger was
verified, and four generated CSV files were normalized from CRLF to LF. A later
source-only canonical-notation migration changed the TeX but did not rebuild
the PDF. No hostile mathematical audit, repository-wide novelty review,
experiment replay, full canonical-preamble normalization, figure regeneration,
or PDF rebuild has yet been performed. The manuscript's theorem labels and submitted numerical files
do not by themselves establish Lean proof status.

The submitted PDF remains the 36-page A4 artifact. It is openable and
unencrypted, and all 39 font records are embedded and subset, but 11 records
come from Type 3 plot fonts. The submitted source uses 25 mm margins rather
than the repository's canonical 27 mm article preamble. These are recorded
intake limitations, not repaired facts; see `PDF_VALIDATION.txt`.

## Arrival provenance

The source archive was
`drafts/incoming/geometric_comb_interpolation_report-3.zip` (1,296,171 bytes;
SHA-256
`89c9de31b9b78b614c13d5a3ff24ae41b73ef6704a9daef77ba724b396e90fa0`).
It contains 24 ZIP entries: three directories and 21 regular files. Its
submitted self-excluding 20-entry ledger has SHA-256
`0d56124e8fd39cdbcef7e70307716f0124963166aaf40ebe4f45942127fd6144`
and is preserved byte-for-byte as `SHA256SUMS.arrival.txt`; all 20 listed
payload hashes verified before normalization.

This arrival is not a reship of the existing
`geometric_comb_interpolation_report/` package. The two packages have no
byte-identical non-ledger files, different source and PDF hashes, different
titles/bodies, and different data/figure inventories. The package is now
registered at this canonical path; the incoming ZIP has been removed from the
working tree, with its outer hash and Git history retaining the archive
receipt.

## Contents

- `geometric_comb_interpolation.tex` — current notation-migrated source;
- `geometric_comb_interpolation.pdf` — retained submitted PDF, pending rebuild;
- `geometric_comb_experiments.py` — submitted experiment generator;
- `data/` — four submitted CSV tables, normalized to LF in the live package;
- `figures/` — five submitted plots in both PDF and PNG form;
- `NUMERICAL_SUMMARY.txt`, `README.txt`, and `requirements.txt` — submitted
  notes and unpinned requirements;
- `ARRIVAL_MANIFEST.txt` and `SHA256SUMS.arrival.txt` — immutable arrival
  bookkeeping;
- `INTAKE_AUDIT.md` and `PDF_VALIDATION.txt` — quick-gate records;
- `SHA256SUMS.txt` — unrefreshed 25-entry operational ledger, excluding itself;
  its TeX, README, and relocated intake-audit rows are pending.

The submitted reproduction command, not replayed at this gate, is:

```bash
python -m pip install -r requirements.txt
python geometric_comb_experiments.py --output-dir . --max-order 80
```
