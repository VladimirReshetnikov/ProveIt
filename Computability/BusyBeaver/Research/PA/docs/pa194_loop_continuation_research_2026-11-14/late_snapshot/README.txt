LATE SNAPSHOT ADDENDUM
=====================

Initial snapshot: 32d0d8b7d93a63ad4106c18cdb29b37927acdad2
Latest checked snapshot: 603c58ca3bd6bf3222fcfc4e308e6b079f65d573

The repository advanced during preparation. This folder records the new
evidence separately. The original 82-packet ledger and 94-graph census in
comparison/ are preserved; their assertions remain pinned to the initial
snapshot.

The complete repeated census at the later snapshot recognizes 110 spanning
194-state classes: the original 94 and 16 additions. All originally recognized
graph classes are still represented. Five additions are reported principal
constructions (AX11G, AX11QH4L, AX11QH4R, GH, GHS); eleven are research inputs,
not eleven additional accepted consistency machines. The count at 193 states
remains 53. The general complete-spanning count is 680 under the same documented
literal/explicit-JSON recognizers.

The five latest incoming ZIP payloads comprise four new archive names and
one revised AX11H archive. Their exact Git blob IDs, SHA-256 hashes, byte
counts, old-revision identity where applicable, and top README hashes are
recorded in archive_manifest.json/csv. The five former incoming packets have
been filed under PA/docs; there are now 82 filed directories. The two AX11H
delivery versions must not be silently treated as the same evidence.

OFFLINE NOVELTY REPLAY

From the release root:

  python3 -B late_snapshot/check_novelty.py

This uses the 94 existing frozen representatives plus the 16 exact tables in
representatives/. Every reference is bound to its hash. It compares full
canonical tuples, allowing all working-state renamings, every spanning root,
reflection, global bit exchange, and ignored terminal write/move effects.
It does not treat a bit exchange as preservation of a fixed zero blank.

The four primary-source LC graphs and PA194LC_AX11H are new against all 110
and mutually distinct. The initially constructed GAX11 table is exactly the
late AX11G graph L01 and is explicitly not claimed new in this addendum.
The candidate bytes in candidates/ are frozen inputs for this comparison;
their construction and proof obligations are documented elsewhere in the
release. Structural novelty alone proves no consistency theorem.

FULL CENSUS REPLAY

To independently repeat the complete latest census using a Git checkout
containing the latest commit and its blobs:

  python3 -B late_snapshot/rebuild_census.py --repo /path/to/ProveIt --output /tmp/pa194-late-census

This uses the same attributed recognizers as the initial audit and verifies
every source blob's exact identity. A Git checkout is needed only for this
full corpus repetition; the novelty replay above is entirely offline.

FILES

  late_comparison.json       Combined summary, new archives, class identities,
                             novelty results and source-status qualifications.
  latest_full_census.json    Complete later census; separate from the old census.
  latest_full_summary.json   Later counts and recognizer error record.
  delta_classes.json/csv     L01--L16, full hashes, locations and occurrences.
  all_added_classes.json    All 22 newly recognized spanning classes, including
                             six larger auxiliary graphs outside the 194 slice.
  representatives/         Exact normalized tables for L01--L16.
  candidate_manifest.json  Exact frozen comparison inputs and their claims.
  novelty.json             Observed completed full-tuple replay.
  archive_manifest.json/csv Exact identities of the five incoming ZIPs.
  source_status.json       Official formal-status changes and new packet claims.
  PA_README_delta.diff     The official PA status change, verbatim as a Git diff.
  latest_PA_README.md      Exact latest official PA README.
  source_readmes/          Exact top READMEs of the five latest ZIPs.

The revised AX11H packet introduces an ordinary written absolute iPRA
calibration claim. The official maintained PA README still leaves the
machine-specific absolute endpoint open. This folder records the new claim
and its provenance; its mathematical use is addressed separately in the main
report and does not follow from the census or executable novelty check.
