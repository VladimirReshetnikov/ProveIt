# Provenance and retained notices

This research package was prepared for Vladimir Reshetnikov in response to a
request to compare the supplied Con(U)/Con(PA) U212 candidates and produce a
candidate below 212 states. New material is the guarded nine-rotation U211
construction, its proof and source/runtime integration, the portable builder
and driver, independent source/startup audits, final-fold certificate, and report.

All ProveIt source downloads were pinned to commit
`9d50bf3df8c9e14941b549945c4f8400172d81f4`. Exact source URLs, Git blob SHA-1
identities, byte lengths and archive SHA-256 values are retained in the manifests.

The common U212 table, source, and inherited calibration are the work supplied
in the user's linked ProveIt research directory. In particular:

- `code/symbolic_runtime.py`, `code/independent_runtime.py`, and
  `inputs/legacy_mapping.json` are copied unmodified from
  `U212_ConPA_Stacked_2026-10-28 (1).zip`.
- The baseline literal table/source are the byte-identical objects in all
  complete U212 packets. The source's duplicate copies are not new proofs.
- `reference/u212_combined_2026-10-29.zip` and
  `reference/pa_unary_power_cover.zip` are included intact, preserving their
  original internal attributions, notices and license files.
- Additional retained ProveIt and Wade notices are in `reference/licenses/`.
- The fixed K215/Con(ZFC) development and Theory K are background credited in
  the report. Their kernel theorem is not represented as certifying U211.

The symbolic engine's original docstring mentions proof-note paths in its
source archive. It is deliberately unchanged for provenance. The equivalent
discussion for this package is in `paper/runtime.tex` and
`evidence/runtime_rule_notes.md`; the complete retained baseline is included.

Audit notes under `evidence/` preserve some preparation-time paths and labels.
They are explanatory records, not dependencies of `reproduce.py`. All active
verification paths are relative to the extracted package.

No authorship of the inherited theories, proof-search compiler, or earlier
state reductions is claimed for this new research step. The proof-status
qualification in the report applies to all generated summaries and artifacts.
