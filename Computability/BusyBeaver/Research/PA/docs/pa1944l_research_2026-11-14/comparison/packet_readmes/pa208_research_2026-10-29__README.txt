PA CONSISTENCY MACHINES: COMPARISON AND RESEARCH BELOW 208 STATES
29 October 2026

READ THIS STATUS FIRST
======================
This archive does not establish a valid machine below 208 working states.
It provides the requested comparison and new research, including eighteen
new, pairwise non-isomorphic 208-state machines with elementary local
halting-equivalence proofs. The numerical goal remains unmet.

Start with report.pdf (full report) or report.tex (complete LaTeX source).
Every factual claim distinguishes ordinary mathematical proof, an auditable
symbolic induction engine, a finite rejection screen, and a proof-assistant
certificate. No new end-to-end PA, MM0, Lean, or Rocq certificate is claimed.

PRINCIPAL RESULTS
=================
1. The five supplied U208 proposals have only TWO rooted action-preserving
   transition-graph classes. All perform the same historical 172/211 fold.
   Their savings cannot be combined.
2. Fresh full symbolic replay passed for both originals: 5,084 arbitrary-
   natural primitive contracts per table, all 416 rows covered, and the exact
   48,140-step blank startup. All five quick upstream drivers also passed.
3. Four new merge/helper constructions yield 18 new 208-state graphs (nine per
   baseline), all distinct from one another and from both original graphs.
   Their proofs use a complete one-step incoming census and exact positive
   two-cell blocks of length 1, 3, or 5. The standalone checker uses only Python's
   standard library. The attempt to share one helper between two merges,
   which would give 207 states, produced no surviving candidate.
4. A new directional source-associativity theorem needs only forward closure
   of the first factor and backward closure of the last. It permits an open
   middle factor and halt occurrences.
5. Direct arithmetic negation uses 18 rather than 47 primitives. Replacing all
   six occurrences saves 174 instructions, with the same formula outputs.
   The source has 3,735 primitive occurrences and 198 DAG nodes; the tested
   six-occurrence literal allocation still required 212 states.
6. Fixed-role covers preserve the native logical interface and save 37
   primitives. The best recorded source has 203 DAG nodes, versus 197 originally.
7. Removing successful-MP padding is supported by a corrected final
   three-command proof compiler with an explicitly reserved zero. An
   independent inductive zero certificate includes the actual interior
   startup. Its tested allocation has 209 states, not 207.
8. Direct S25/S26 selection macros implement the old command for all natural
   cache values, but their source-DAG counts increase. Further local searches
   and explicit false-positive counterexamples are included.

CONTENTS
========
report.tex / report.pdf        Complete exposition and proofs.
sources_manifest.json          Repository commit, exact Git blob IDs, sizes.
MANIFEST.json                  SHA-256 hashes of the delivered files.
upstream/*.zip                 The six exact pinned input archives.
upstream/README.md             The pinned incoming-directory README.
code/verify_helper_machines.py Independent 18-machine local-proof checker.
evidence/                      New independent proof receipts and replay logs.
analysis/candidate_comparison.md
analysis/directional_associativity.md
analysis/theory_audit.md       Detailed audit notes.
analysis/comparison/double_helper/
                              All 18 new tables, proofs, hashes, exact local
                              certificates, and finite regression receipts.
analysis/runtime_redesign/    Negation, fixed-cover, and arithmetic work.
analysis/reduction_search/    Context/local searches, MP and S source changes.
analysis/offset_search/       Offset, marker, and finite-frame search code.
analysis/compiler_upstream/  Experimental allocation and its outcomes.
analysis/emitter/lineage/     Selected small retained source/proof dependencies.

The table files under augmented_A_* and augmented_B_* in double_helper are
the eighteen accepted new 208-state alternatives. The names candidate, PASS,
or source in other experiment directories do NOT assert full correctness.
Many files record deliberately rejected or finitely screened candidates.
Read analysis/EXPERIMENT_STATUS.txt before treating any experiment as evidence.
Each accepted directory also supplies machine.dense.tm with working labels
0 through 207 and halt label 208, plus the exact native-to-dense state map.

REPRODUCTION
============
Use Python 3.10 or later, from this archive's root directory:

    python3 -B reproduce.py

This checks every delivered-file hash, verifies and safely extracts the
bundled pinned archives, independently checks all 18 helper proofs, rechecks
the two original graph classes, the 58 directional source transformations,
the inductive zero certificate, the MP source splice, and the six direct-
negation replacements. Detailed outputs go to evidence/replay/.
Do not use Python -O: several inherited audit scripts use assertions.

For the full fresh symbolic replay of both ORIGINAL 208 graphs (a few minutes):

    python3 -B reproduce.py --full

The original completed receipts are already included. The local proof
checker establishes halting equivalence of each NEW 208 table independently
of finite primitive tests, so no new full runtime export is required for
that local theorem. It does not prove PA consistent or the machine nonhalting.

Optional finite regression for all 18 new tables (requires a C++17 compiler):

    python3 -B reproduce.py --finite

Build the PDF from the complete TeX source with TeX Live or an equivalent:

    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The quick proof checks need only Python's standard library. Optional research
scripts have additional dependencies: the vectorized window tools use NumPy;
allocate_current.py uses z3-solver (tested 5.3.3); inherited allocate.py uses
NumPy/SciPy. Compiled search executables and large regenerable window bitmaps
are omitted. Their C++ sources and input/receipt files are retained. The
canonical one-step helper proof does not require those window bitmaps.

PROVENANCE AND LIMITATIONS
==========================
All six inputs are pinned to ProveIt commit
c086b5adaa6228009365768946d691dfc49a20bb.
Their exact byte hashes are listed in the report and source manifest.
The archives retain their original licenses and attribution. Selected
extracted dependencies retain their notices. New report/proof/checker work
is identified separately; it does not replace or claim authorship of the
underlying machine architecture, theory, calculus, or runtime verifier.

The smaller-source experiments are ordinary mathematical/source results;
the accepted new literal machines remain at 208 states. Negative searches
are bounded or restricted families, never a lower bound on arbitrary
PA-consistency machines. The desired sub-208 construction remains open here.
