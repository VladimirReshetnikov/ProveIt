COMPARISON AND NOVELTY EVIDENCE

Pinned repository: VladimirReshetnikov/ProveIt
Commit: 7c0bb454cf73c29ca1c385f9fec856ddd236a7cb

Read comparison_notes.md for the counting convention, design comparison,
new incoming designs, rejected193 examples, and proof-status distinctions.
named_designs_104.csv maps every catalogued named positive-claim graph to a
current exact source and its freshly recomputed canonical identity.
mechanism_families.csv gives43 descriptive groups, not43 independently
verified consistency theorems.

Offline novelty replay (Python3 standard library):

  python3 comparison/verify_novelty.py PATH_TO_FIRST_MACHINE.tm PATH_TO_SECOND_MACHINE.tm

This checks every reference table hash, reconstructs its exact canonical
tuples, verifies548 spanning and two nonspanning194-control references,
and compares candidates under arbitrary spanning roots and control names,
tape reflection, global symbol exchange, and ignored halt-edge actions.
The arguments can point to any complete194-state dense table with start0
or another explicit '# start N' header. Add --output FILE.json to save a
receipt. No original repository or network is needed for this replay.

The code intentionally compares exact tuples rather than only hashes.
Global symbol exchange is a stronger cosmetic-novelty test, not a claim
that complementing symbols preserves the specified zero-blank semantics.
Graph novelty does not prove machine correctness or PA calibration.

global_associations_novelty.json records the wider63-candidate batch.
It contains62 new mutually distinct classes and one correctly recognized
old graph, A0M2L11_194 = PA194ORH. Its recorded table paths refer to the
research workspace, while the selected final machines are packaged by
the main report. The frozen reference_tables directory is self-contained.

To rebuild the explicit-table census from an exact Git repository with
the pinned objects available:

  python3 comparison/rerun_census.py --repo PATH_TO_ProveIt --output NEW_CENSUS_DIR

The driver obtains the pinned tree with git ls-tree, verifies local file
bytes against Git blob hashes and uses git show for differing or missing
working files. It recursively reads ZIPs and recognizes the documented
explicit TM/JSON encodings. It does not execute arbitrary generators.
See census_summary.json for the complete scope, exclusions and counts;
census_verified_sources.json binds all15,727 selected tracked payloads.
census_occurrences.csv maps the7,331 recognized table occurrences to
their normalized content and spanning canonical class when one exists.

ATTRIBUTION.txt identifies the inherited parser/canonicalizer and ledger.
The new driver, current corpus verification, incoming extensions and
fresh candidate comparison are supplied by this research exercise.
