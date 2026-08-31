# Companion-asset policy

The pre-retirement audit of the ten later source directories and the canonical
package found no byte-identical companion files, even after LF normalization of
text. Apparent duplication is semantic: similarly named files often use
different degree ranges, normalizations, grids, or operators.

## Selected payload

The canonical package retains exactly 113 selected payloads:

- every independent executable reproducer;
- every exact rational CSV, TeX table, symbolic certificate, and captured
  exact output;
- useful diagnostic PNGs;
- environment and requirements inputs needed for reproduction;
- the exact Q12 Sturm certificate, root-count table, and verifier.

Of these, 111 are grouped by source-directory slug under
`assets/companion-evidence/`; the Q12 certificate and complete root-count table
already had byte-identical canonical destinations under
`assets/evidence/legendre/root-geometry/`. Several scripts collide on names such
as `experiments.py`, so flattening them could discard independent checks.

`COMPANION_PAYLOADS.csv` maps every old path to its one live destination and
SHA-256 hash.  `assets/companion-evidence/SHA256SUMS` verifies all 113
destinations, including the two relative paths into the root-geometry evidence
tree.

## Generated and historical material

Generated diagnostic images and logs are not mathematical authorities; scripts
and exact data are. Historical README, MANIFEST, repository-snapshot, and source
files remain recoverable at immutable pre-retirement commit
`443793e846934e7363e314ea01129b9f50197a58`. Historical package checksum files
are retained with the companion evidence as arrival provenance; they are not
presented as current live ledgers.

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

## Exact retirement gate -- completed 2026-08-31

Every required condition was discharged before the ten old report directories
were removed:

1. Every proved source result has an auditable canonical crosswalk: 80
   theorem-like environments, 80 proofs, and 80 one-to-one crosswalk rows.
2. All 113 selected payloads have canonical destinations and live hashes in the
   companion mapping and ledger.
3. Distinct coefficient normalizations and degree ranges are documented in the
   canonical chapters and assertion-level crosswalk.
4. The v6 missing-at-arrival boundary remains explicit here, in the README, and
   in the canonical source.
5. The Q12 verifier and canonical certificate paths pass through degree 20.
6. The canonical PDF passed three direct TeX runs, full-page rendering, log
   audit, and a zero-Type-3 font scan.
7. The live root `SHA256SUMS` validates canonical Git-tree bytes from a fresh
   checkout.
8. Historical arrival ledgers are retained, while source snapshots remain
   recoverable at the immutable pre-retirement commit above.

The exact directories retired by this gate are:

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
