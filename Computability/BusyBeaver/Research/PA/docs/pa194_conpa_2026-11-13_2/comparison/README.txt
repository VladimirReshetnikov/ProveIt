Comparison and input-corpus audit
=================================

Source snapshot: VladimirReshetnikov/ProveIt at
5be8b9236df6a6d308195e62a906a173dc70d00a.

The principal comparison is:

  Design                     States   AX tokens   Source sites   Allocation
  Published PA196              196        201          3812       inherited design
  Archived separate196         196        190          3673       134 + 68 - 6
  Supplied PA195               195        191          3700       134 + 68 - 7
  New separate195 intermediate 195        190          3673       134 + 67 - 6
  New PA194                    194        190          3673       134 + 68 - 8

The allocation columns count inherited working controls, AX reader controls,
and simultaneous compatible folds. The new PA194 does not reduce the logic
to a weaker consistency statement. It implements the archived separate190
calculus, with its explicit ten-entry original-command compiler, and has the
PA-provable consistency biconditional proved in mathematics/pa194_calibration.tex.

The separate195 intermediate is preserved here with a self-contained builder.
It is useful evidence that minimizing reader count alone is the wrong cost:
one additional reader can permit two additional compatible folds. The primary
deliverable is ../pa194/pa194.tm, not the intermediate table.

Corpus scope
------------
corpus/source_manifest.json gives exact Git blob digests, SHA-256 digests,
filenames and pinned URLs for all 32 docs/incoming entries, including the
31 ZIP archives. The recursive census recognizes complete five-column binary
transition tables in numeric .tm or .txt members, plus direct PA .tm files.
It is not a census of arbitrary tables embedded in JSON, prose, or source code.
It includes duplicates, diagnostic candidates, controls and rejected tables;
inclusion is not evidence of correctness.

The fresh input census records 2,719 table occurrences, 576 distinct raw table
byte strings and 566 distinct labeled transition functions. The 31 top-level
ZIPs occupy 233,712,151 bytes; recursive nesting contains 198 ZIP occurrences
and 44 distinct ZIP payloads. There are 17 195-state table occurrences,
10 byte strings and seven rooted action-graph classes: the supplied PA195
and six earlier rejected or uncertified diagnostic classes. Starts are taken
from explicit supplied conventions, never guessed from a state number.

No recognized table in that pinned input census has 7 through 194 working
states. This statement excludes the new outputs of this task. It is neither
a mathematical lower bound nor a claim that every possible encoding of a
table was recognized.

Archive comparison
------------------
corpus/archive_catalogue_current.json gives an entry for every one of the
31 archives. The first 27 descriptions explicitly attribute their narrative
to the supplied PA195 comparison, with current archive bytes independently
verified. Four additional archives were read separately: PA195 itself,
pa_consistency_cross_archive.zip, pa_consistency_reduction_audit_2026-11-14.zip,
and pa_consistency_research_2026-11-14.zip. The last three add complete 196
or 197 state combinations, including H-only Shift, MP-in-H, zero jumps and
the NEG18 source macro. These are informative comparisons; none of their
changed command interfaces is silently imported into the PA194 proof.

The detailed baseline proof review and current-archive findings are in
../mathematics/proof_and_comparison_audit.txt. The preserved PA195 package
contains its earlier 27-archive comparison and larger-design inventory.

Reproduction
------------
Put the exact pinned archives in a directory ARCHIVES with the manifest's
filenames. With a checkout of the pinned repository at REPO, run:

  python comparison/census_current.py --archive-dir ARCHIVES \
    --pa REPO/Computability/BusyBeaver/Research/PA --out replayed_census.json
  python comparison/compare_195.py --archive-dir ARCHIVES \
    --census replayed_census.json --out replayed_195_classes.json

Run these commands from the package root. The parser verifies each archive's
Git blob before inspecting it. The separate195 intermediate is checked by
running python build_verify.py from comparison/separate195. The main new
machine has its own builder and independent verifier as explained in the
top-level README.

Exploratory searches
-------------------
searches/bounded_search_ledger.json records fixed random seeds, exact input
blobs, completed cycle counts and output logs for five additional association
searches. A cycle has 3,000 mutation slots; skipped mutations and repeated
shapes are included. Those counts are not distinct candidate machines or
score evaluations. Matching estimates for the h1/h2/h6 logical relocations
were not promoted to accepted literal machines. No negative search record
asserts impossibility below the best result it happened to find.
