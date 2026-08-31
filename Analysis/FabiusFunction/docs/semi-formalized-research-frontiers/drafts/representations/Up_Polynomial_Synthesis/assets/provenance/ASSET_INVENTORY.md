# Companion-asset policy

The ten later source directories plus the canonical package contain no
byte-identical companion files, even after LF normalization of text. Apparent
duplication is semantic: similarly named files often use different degree
ranges, normalizations, grids, or operators.

## Selected payload

The migration plan retains 113 unique payloads:

- every independent executable reproducer;
- every exact rational CSV, TeX table, symbolic certificate, and captured
  exact output;
- useful diagnostic PNGs;
- environment and requirements inputs needed for reproduction;
- the exact Q12 Sturm certificate, root-count table, and verifier.

Original scripts remain grouped under their source-directory slug because
several collide on names such as experiments.py. Flattening them before a
common orchestrator covers every output could discard independent checks.

## Generated and historical material

Generated diagnostic images and logs are not mathematical authorities; scripts
and exact data are. Historical README, MANIFEST, repository-snapshot, and
checksum files are arrival provenance. They must not be presented as current
live ledgers.

Legacy ledgers contain 142 entries: 123 verify raw and 19 differ only because
arrival ledgers hashed CRLF bytes while the repository stores LF. The
Legendre-v3, Legendre-v4, and self-reconstruction ledgers verify fully. The
base Lagrange report and v6 have no ledger.

## Type 3 hazards

Do not embed these old vector figures in the canonical report:

- all four PDF figures from Lagrange_Rvachev_Closed_Loop_Report;
- both PDF figures from Rvachev_Lagrange_Loop_Report_v5;
- all four generated PDF figures from Legendre_Rvachev_Self_Reconstruction.

The v5 and self-reconstruction figures have PNG twins. The four Lagrange
closed-loop PDFs have no PNG twins and remain provenance-only until regenerated
with embedded Type 1 or OpenType fonts.

## Exact retirement gate

Only after every condition below is satisfied may the ten old report
directories be removed:

1. Every proved source result has an auditable canonical crosswalk.
2. All 113 selected payloads have canonical destinations and live hashes.
3. Distinct coefficient normalizations and degree ranges are documented.
4. The v6 missing-at-arrival boundary remains explicit.
5. The Q12 verifier and canonical certificate paths pass.
6. The canonical PDF passes three direct TeX runs, full-page rendering, log
   audit, and a zero-Type-3 font scan.
7. A live root SHA256SUMS validates canonical Git-tree bytes from a fresh
   checkout.
8. Historical arrival ledgers and source snapshots remain recoverable.

The exact removable directories are:

- rvachev_lagrange_loop_report
- Lagrange_Rvachev_Loop_Package
- lagrange_rvachev_loop_report_v3
- Lagrange_Rvachev_Closed_Loop_Report
- Rvachev_Lagrange_Loop_Report_v5
- Rvachev_Lagrange_Loop_Report_v6
- legendre_rvachev_closed_loop
- Legendre_Rvachev_Closed_Loop_Report_v3
- Legendre_Rvachev_Closed_Loop_Report_v4
- Legendre_Rvachev_Self_Reconstruction

No broader glob or parent directory is authorized by this plan.
