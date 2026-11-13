REFERENCE SOURCES AND BASELINE CONTROLS
======================================

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: e88ebf229bb61bd870bb229b9c97caaa1e044e6e
Subtree: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

These files are inherited reference material, not newly proved theorems or
new checker implementations. PROVENANCE.json records each selected original
repository path, archive member when applicable, verified Git blob identity,
and local SHA-256. The accompanying MIT No Attribution license is preserved.

CONTENTS

controls/ contains seven complete incumbent Python programs:

  compact_tokens239.py     239 tokens / 261 AST nodes / 549 normalized bytes
  compact_ast255.py        245          255             580
  compact_bytes460.py      266          299             460
  sorted_tokens302.py      302          352             646
  sorted_ast340.py         314          340             681
  sorted_bytes584.py       311          362             584
  exact_bytes1424.py       581          641            1424

The compact programs require a canonical guarded public goal and an exact
integer/list input alphabet. The sorted programs validate the full parsed
alphabet and a broader sorted goal grammar. Their theorem-completeness claim
is restricted to the canonical encoder image; it does not hold for every
padding-slot spelling admitted by that broader grammar. The exact control
checks the canonical encoder image itself. These are different contracts.
The compact and sorted coordinate envelopes are attained by different
programs. These are observed finite-corpus records, not mathematical lower
bounds. The exact program is the matched exact-syntax control used here;
no global optimality claim for that control is made.

Lean/ contains selected exact upstream source files for the native calculus,
ordinary theories, interpretations, and both formula round trips. See
FOUNDATION_THEOREMS.txt for declarations that were actually inspected. This
selection is not a complete independently buildable Lean project: transitive
imports and the upstream mathlib/toolchain are not bundled. No new Lean build
or formal verification of Python execution is claimed.

article/ contains the exact pinned ch01_base.tex and ch11_cert.tex. These
are source references for the inherited mathematics and checker protocols.
They are not needed to compile the new report and are not standalone TeX
documents by themselves.

prior_source_census.json.gz is the unmodified content of the existing source
census included in the pinned 304-token incoming archive, compressed here for
space. artifact_source_tree.json.gz is the current pinned Git tree inventory
of all 3542 .py/.py.gz artifact entries. Their uncompressed identities and
source origins are recorded in ../evidence/baseline_census_reference.json.
The current tree audit reuses measurements only for exact unchanged Git blob
identities; the 14 newly fetched unmatched entries are retained in audit_delta/.
These include test drivers and measurement utilities and are not all proof
checkers. Static source coverage does not semantically certify every program.

The detailed comparison and provenance receipts are:

  ../evidence/baseline_controls.json
  ../evidence/baseline_tree_audit.json
  ../evidence/baseline_archives.json
  ../evidence/baseline_census_reference.json

reader_companions/ retains the two independently tested local-scope exact
expression checkers used to establish the reader theorem, their translated
positive/negative fixtures, and a self-contained verification script. These
are supporting variants, not the selected global-scope minima of the report.
Their metrics and receipt are ../evidence/reader_companion_metrics.json and
../evidence/reader_verification.json. To repeat that supporting evidence:

  python3 reference/reader_companions/verify_expression_reader.py

No GitHub repository content was modified by preparing this archive.
