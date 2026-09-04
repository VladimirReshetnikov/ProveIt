# Retained companion evidence

This tree is the canonical home of the non-prose payloads retained from the ten
Lagrange--Rvachev and Legendre--Rvachev reports absorbed into
`Up_Polynomial_Synthesis`.  Source-directory slugs and relative paths are kept
intact so scripts with colliding names, distinct normalizations, and generated
tables remain unambiguous.

The migration accounts for exactly 113 selected payloads:

- 104 mapped payloads live below this directory (105 files including this
  README);
- the exact `Q12_sturm_certificate.txt` and
  `sturm_real_root_counts.csv` already had byte-identical canonical homes under
  `../evidence/legendre/root-geometry/`.

The old-to-new path, hash, and disposition of all 113 historical selection
rows are recorded one-to-one in `../provenance/COMPANION_PAYLOADS.csv`. It maps
106 live destinations and preserves seven retired checksum-ledger rows without
live destinations.

The absorbed report TeX, compiled PDFs, report-level READMEs, dated audit and
snapshot files, and ten Type-3-bearing vector figures are intentionally not
duplicated here.  They remain recoverable at immutable pre-retirement commit
`443793e846934e7363e314ea01129b9f50197a58`; useful PNG twins are retained when
available.  The v6 report arrived without the companion files named in its
prose, and this migration does not invent them.

Historical package checksum files describe arrival layouts and may encode
pre-normalization line endings. They are retired from the current tree and
remain recoverable from the immutable pre-retirement commit; the provenance
map preserves their hashes.
