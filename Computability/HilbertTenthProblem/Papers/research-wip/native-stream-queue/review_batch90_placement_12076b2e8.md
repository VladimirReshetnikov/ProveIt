# Bounded byte-placement review of batch 90

At commit `12076b2e8b4806efe46b1588926eeed2809c0952`, all 32 added files, totaling 371,628 bytes, are byte-identical to members of the six previously reviewed archives at arrival `a162e4386fa8a1beaef58a565c2205ba5fb5c270`. All 53 archive members were reauthenticated against the earlier intake pins. No content mismatch was found.

The placement resolves the source-file location for the new **Cantor families of surreal subfields** report: its `article.tex`, README, source audit, code and data are now present under `Algebra/SurrealNumbers/docs/foundations-and-computation/cantor-families-of-surreal-subfields`. The article and README are unchanged delivery bytes. The previous intake read the full README; it did not certify the whole 1,843-line article. This byte comparison does not enlarge that mathematical review scope.

The remaining five manuscripts have ancillary evidence placed, rather than their article/guide integrations completed at this commit:

| Intended manuscript placement | Evidence actually added | Existing article and README |
|---|---|---|
| Named symmetries, hereditary-sets Part VIII | Prefixed audit, Makefile, checker and data | Both unchanged |
| Local codes, Polish arithmetic Part XI | Prefixed proof-status/source-audit, checker and data | Both unchanged |
| Polish completions, Polish arithmetic Part XII | Prefixed proof audit and build script | Both unchanged |
| Perfect transcendence gaps, discrete initial subgroups | Prefixed source audit/theorem ledger, checker and data | Both unchanged |
| Hat surplus, measurable box games Part II | Prefixed audit, license, code README, scripts, data and two figures | Both unchanged |

This distinction follows from exact parent/child byte comparisons, not solely the placement commit message. The four existing host articles have unchanged label counts 296, 784, 236 and 65 respectively; none contains the intended new `hset:ns:`, `pma:lgc:`, `pma:gcm:`, `isg:ptg:` or `mbg:hat:` labels. The eight host article/README files were compared in full as bytes, not reread in full as mathematical prose. In particular, the previously completed Polish Part X remains present, while the proposed Parts XI and XII are not yet inserted at this frozen commit. This is an integration-status checkpoint, not a theorem defect or an assertion about later work.

All six ZIPs were removed from `docs/incoming` in this commit and remain recoverable at the pinned arrival. The one non-addition text change is `SetTheory/Cardinals/.gitattributes` lines 232–234, read in full as a delta: it marks the delivered hat prefix CSV `-text`. The fresh comparison confirms the CSV retains its original CRLF bytes. The two placed hat figures were compared as bytes only, not rendered. The six manuscript PDFs were not placed or read in this review.

`review_batch90_placement_12076b2e8.json` records every archive/member pin and prior coverage, every new path and Git blob, its exact matching archive member, and the parent/child hashes of unchanged host files. Prior coverage transfers only across exact byte equality; unread source audits, code, and articles remain unread. The earlier intake receipt is pinned at SHA256 `3eb296146ce0233db75deb835e7568ace428f247399e6252a1131bd570e290f8`. Its scope and source claims remain immutable.

The fresh helper `review_batch90_placement_checks.py` used only read-only Git operations, ZIP/JSON decoding, byte comparison and a label census. No supplied scripts, audit adapters, builds or Lean were executed or imported. `Algebra/SurrealNumbers/AGENTS.md` was read; this is a documentation-only review with no repository edits. No new paid arithmetic compiler is established by this placement audit.

Helper SHA256: `cfac66e55ed6d88e870385fef773fb2ef6b72e297aec370e44067f0d44b6e4ff`. Inventory/check receipt SHA256: `ac1be17dc90315b7fbc2679d24477dfecafcb64c3d9552b1888ffa777fdf049c`.
