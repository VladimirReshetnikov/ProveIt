COMPARISON, CENSUS, AND NOVELTY RECEIPTS
======================================

Pinned source
-------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 17f92105e2bc4317feae6c219cb2143437b482ff

The historical corpus is frozen at that commit. The new PA194J, PA194D,
and sibling constructions in this delivery are compared against it; they
are not included retroactively in the historical census totals.

41 packets are not 41 distinct machines
--------------------------------------
archive_ledger.csv and archive_ledger.json cover all 36 filed research
packets under Computability/BusyBeaver/Research/PA/docs and the following
five incoming archives, whose contents were not yet filed there:

  pa194C_conpa_2026-11-13 (2).zip
  pa194_new_designs_2026-11-13.zip
  pa194c_conpa.zip
  pa194c_conpa_2026-11-13 (1).zip
  pa194c_conpa_2026-11-13.zip

The ledger distinguishes principal constructions, supplementary variants,
search inputs, rejected candidates, repeated tables, and audit-only work.
Its descriptions and evidence status come from the supplied packet files.
State counts and table identities were independently recounted. The
inventory does not rerun every historical proof certificate and does not
certify every legal transition table as a Con(PA) construction.

Numeric-table census
--------------------
census/census.json records the exact scope, occurrences, archive traversal,
byte identities, graph identities, and source locations. census/tables/
contains the 620 byte-distinct recognized tables, named by SHA-256.

The recognizer reads tracked .tm/.txt/.tsv/.csv files under the PA research
directory, recursively reads its nested ZIPs, and recursively reads the
five new archives. Repeated ZIP bodies are scanned once. A recognized
table must contain complete deterministic numeric rows for both binary
symbols at every working control, with exactly one undefined halt label.
It does not extract transition tables encoded only in JSON, Python, Lean,
or prose. Thus these are explicit-table census totals, not a count of all
programs that the repository could generate.

  Suffix-selected file occurrences examined:       4570
  Recognized complete table occurrences:           2685
  Byte-distinct recognized tables:                  620
  Root-free action-graph classes:                   446
  Unrootable synthetic table controls:                2
  194-state occurrences / byte forms / graph classes: 95 / 15 / 8

The two unrootable controls have 6 and 9 states and are disconnected test
fixtures, not smaller PA constructions. The absence of an accepted
sub-194 result is not a lower bound on what can be constructed.

Graph signatures use ordered read-0/read-1 traversal, retain the written
symbol and head direction, replace working labels by traversal ordinals,
and use a distinguished halt target. Taking the least serialization over
all roots reaching all working controls removes the distinguished start
control. The 194-state comparison additionally allows a global L/R
reflection and a global read/write bit complement. Different resulting
signatures therefore exclude state renaming, even with those additional
transformations. These are action-graph comparisons, not equivalence
tests for the functions or computations of arbitrary Turing machines.

Frozen eight-class frontier
---------------------------
frontier194.json and frontier194.csv describe the eight old classes.
frontier194/ stores one literal representative of each class:

  PA194-67          Principal 67-reader, seven-fold construction.
  PA194-67-AD       Physical A/D permutation variant.
  PA194-68          Alternative 68-reader, eight-fold grammar.
  PA194C           Cached controller, 3649 source sites.
  PA194CS          Symmetric Shift, 3646 source sites.
  PA194CZ          Cached scheduler with a known-zero branch.
  PA194-altC       Cached controller on the alternative 68-reader tree;
                   supplied as a checked search input.
  Rejected194-scanner
                   Legal table whose claimed implementation failed on
                   a seven-zero program-address run; not a valid result.

All five newly examined archives repeat the same principal PA194C table.
They also carry secondary constructions that account for additional
classes. Counting file names or archive titles as machines would miss
these distinctions. source_graph_comparison.json records separate source
instruction comparisons, including the equal complete source graphs of
the original 67- and 68-reader constructions and of PA194C and PA195C.

New PA194J family
----------------
new_variants_novelty.json records four new 194-state variants with final
known-zero tests on registers 3, 4, 5, or 6. The register-4 member is the
delivered PA194J in ../construction/. The other three are in
../research/sibling_tables/. Each is distinct from every old 194-state
class and from the other three, even under the transformations above.
The receipt records exact source changes and literal blank-startup runs.

independent_mask_audit.py recomputes the positivity closure for the source
program from the seed and compares the old and new successors at every
reachable abstract pair. It establishes the known-zero premise for all
ten changed source instructions, separately from physical simulation.
The frozen result is A4_independent_mask_audit.json. To replay it from the
delivery root, without modifying the frozen result:

  python3 -B comparison/independent_mask_audit.py \
    --parent references/parent/pa194CS.instructions.json \
    --child construction/machine/pa194j.instructions.json \
    --masks comparison/parent_masksets.json \
    --output /tmp/pa194j_mask_replay.json

New Gamma(D) emitter: PA194D and its CSZ_A sibling
------------------------------------------------
audit_gamma_d.py and gamma_d_independent_novelty.json compare the two new
Gamma(D) tables with the frozen eight-class frontier and all four J-family
variants. Both have 194 working states and are mutually distinct. PA194D
is the CZ member in ../logical_emitter/. The CSZ_A sibling is in
../research/gamma_d_csza/.

The same script independently expands the literal source grammars and
evaluates the AX macro word in a free term algebra, without importing the
compiler, allocator, runtime, or logical proof scripts. It verifies that
the 190-token words differ at zero-based positions 121, 122, and 123 by
copying D instead of A, and at position 189 by the known-zero closing
test. Exactly the last of ten pushed items changes from Gamma(A) to
Gamma(D); the other nine items, parameter reads, and final gate agree.
No global permutation of A, D, H makes the two complete emitters equal.
One concrete witness gives the old last-head code 20 and the new code 832.

From the delivery root, the packaged defaults require no external files:

  python3 -B comparison/audit_gamma_d.py

Use --output /tmp/gamma_d_replay.json to save a fresh receipt. All input
paths are overridable with --old-grammar, --new-grammar, --cz, --csz-a,
--old-frontier, and --j-receipt. --cz and --csz-a specify dense table
files; corresponding native tables and source metadata must be alongside
them. The graph comparison uses the frozen old/J signature receipts. To
recompute an old representative's signature directly, use the included
compare_candidate194.py; its --help documents the generic interface.

This emitter audit establishes a real source-formula change and table
novelty. The source/table binding, universal physical contracts, and PA
calibration are separate parts of the delivery; consult the main report
and the construction evidence. No finite simulation establishes Con(PA).

Reproducing the full historical census
--------------------------------------
The complete repository and the five exact archive bytes are needed for
the original file traversal. Use a clean checkout of the pinned commit,
place only the five archives named above in a separate directory, and run:

  python3 -B comparison/census_current_snapshot.py \
    --repo /path/to/ProveIt \
    --new-packets /path/to/the-five-archives \
    --out /tmp/pa_census_replay

The script checks each of those archive blobs against the pinned Git
object. Its output contains full occurrence lists as well as aggregate
counts. Replaying this census is separate from verifying the new machines;
the root verify.py uses the frozen comparison inputs and does not require
a repository checkout or network access.

Run Python without -O: assertions are part of the audit checks. All
comparison scripts use only the Python standard library.
