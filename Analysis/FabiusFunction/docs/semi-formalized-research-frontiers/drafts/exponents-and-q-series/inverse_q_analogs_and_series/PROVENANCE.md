# Provenance ledger

The canonical volume absorbs the following six source packages.  Paths are
relative to the surrounding `exponents-and-q-series/` directory.

| Source package | Canonical role |
| --- | --- |
| `inverse_q_analog_functions_report/` | Branchwise narrative, parameter selection, real and complex branch atlases, numerical continuation. |
| `inverse_q_analog_jet_atlas/` | Universal inverse jets, Bell-polynomial organization, mixed derivatives, Lagrange-Good inversion, coefficient atlases. |
| `inverse_q_analogs_extended_report/` | Corrected special regimes, certification arguments, radial inverses, and Fabius-Rvachev recovery material. |
| `inverse_q_analogs_report/` | Discriminant and remote-branch analyses, interval and continuation certificates, early conjecture register. |
| `inverse_q_analogs_report-2/` | Independent branch synthesis, reciprocal regimes, compact coefficient tables, algorithmic cross-checks. |
| `q_pochhammer_q_binomial_expansions_report/` | Canonical forward expansion engine for finite and infinite products, Gaussian and multinomial coefficients, roots of unity, and q-special functions. |

The source packages were independently delivered reports, not a linear series
of editions.  Shared titles or formulas therefore do not imply ancestry.  The
concordance records semantic provenance per result rather than selecting a
single package wholesale.

For that reason the consolidation lives in the neutral
`inverse_q_analogs_and_series/` directory.  Although the extended report has
the broadest pre-existing asset layout, promoting it in place would falsely
suggest that the other five packages were merely earlier editions.  They are
peer inputs, and several of their strongest results are absent from the
extended report.

## Source-result inventory

`audit/extract_source_results.py` inventories every theorem-style source
environment before any editorial deletion.  The current six snapshots contain
260 such environments:

| Kind | Count |
| --- | ---: |
| theorem | 131 |
| proposition | 28 |
| lemma | 2 |
| corollary | 16 |
| conjecture | 32 |
| problem | 9 |
| research problem | 19 |
| principle | 4 |
| definition | 9 |
| algorithm | 5 |
| computational result | 1 |
| example | 4 |

The generated `theorem_concordance.csv` retains source package, path, line,
label, result kind, title, enclosing chapter and section, and whether a proof
environment followed the statement.  Editorial columns then record the
canonical label, proof status, Lean counterpart when one exists, and the
reason for merging, correcting, retaining, or retiring the source item.

## Non-TeX asset audit

The six packages contain 65 tracked non-TeX files totalling 5,832,780 bytes:
six Python experiment programs, two requirements files, six READMEs, six
checksum ledgers, six generated report PDFs, twenty generated figures, and
nineteen generated data or audit files.  Four additional untracked files in
the forward-expansion package are ordinary `.aux`, `.log`, `.out`, and `.toc`
build intermediates.

Every entry in all six source checksum ledgers matches its current file.
SHA-256 comparison found no byte-identical pair among the 69 tracked and
untracked non-TeX files.  Similar names therefore do not license deletion:
for example, the three scripts named `inverse_q_analogs_experiments.py`, the
two PDFs named `inverse_q_analogs_report.pdf`, and the two
`qgamma_inverse_branches.pdf` figures all have different contents.

Only two source packages record an immutable repository snapshot:

- `inverse_q_analog_jet_atlas/` records
  `1cea73234a363ddbc392816f6babb5a57920e984`;
- `inverse_q_analogs_extended_report/` records
  `23b19a515ceb44a513b1ec56aeb5c9e99dda5952`.

Both names resolve to commits in the repository.  The other four packages
record no immutable source commit, so their build statements are preserved as
historical package claims, not promoted to current validation evidence.

Unique scripts, captured outputs, tables, and figures are migrated under
`assets/` only when they support a retained theorem, conjecture, or
reproducible calculation.  Because there are no byte-identical assets, any
retirement must instead be justified by proved content coverage and
regeneration parity.  Generated LaTeX byproducts are retired.  The six PNG
previews in the extended package may be omitted when their vector-PDF
counterparts are retained, because no document refers to the PNG copies.
Exact source and destination hashes are appended to the migration ledger
before removal of the old package directories.

All superseded material remains recoverable from Git history after the source
directories are removed.
