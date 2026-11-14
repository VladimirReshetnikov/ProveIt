PA194HAZ — PA consistency at 194 states
======================================

RESULT

No machine below 194 working states was obtained. The package supplies two
complete binary single-tape alternatives, PA194HA and PA194HAZ. HAZ is the
main result: it composes the existing MPH cached-result MP interface, A/D
physical register placement, and a known-zero final AX decrement.

The ordinary mathematical proof in report/pa194haz.pdf establishes, using
the supplied development's unchanged calibration and arithmetic-block lemmas,

  PA proves: not Halt(PA194HAZ, blank) if and only if Con(PA).

The same theorem holds for HA. This is not a new proof-assistant endpoint.
The symbolic executors inherit arithmetic-box contracts. Those assumptions
and the logical proof dependencies are identified explicitly in the report.

The initial candidate H was found byte-for-byte in the supplied N archive
as its auxiliary MPH.native.tm and is not offered as a new construction.
The constituent ideas are prior work. HA and HAZ are new concrete
combinations relative to the complete stated literal-table corpus, rather
than a claim to a new calculus or global priority.

MACHINE CONVENTIONS

Alphabet: 0,1. Two-way infinite tape, initially all zero. Initial head: 0.
Each transition writes a bit and moves one cell left or right.
194 working states; separate halt label.

machine/pa194haz.tm: dense start 0; working controls 0..193; halt 194.
machine/pa194haz.native.tm: native start 74; halt 254.
The corresponding HA files use the same conventions. A labels JSON array
maps dense labels to native labels, including halt as its final entry.
Every .tm file has rows: state read write direction next, LF terminated.

HAZ changes exactly these primary native rows:
  17   1   0 R 32   ->   0 R 48
  144  1   0 R 48   ->   0 R 32
  161  1   0 R 32   ->   0 R 48
  164  1   1 R 98   ->   1 R 130
  2066 1   0 L 302  ->   1 R 21
HA applies only the first four edits. All 194 controls remain graph-reachable.

HAZ native SHA-256:
5ffbc263413612caa71b85895a92860797d90f5c77315119134b6e30fd566f09
HAZ dense SHA-256:
f9f98218e2f949b28f0429f2bbab17babe0f4948c2e38cb786a5e3b239101981

VERIFICATION

Python 3.10+ and recent Node.js standard libraries suffice. Run from the
package root, without Python -O or PYTHONOPTIMIZE:

  python3 build.py
  node verification/verify_haz.cjs
  python3 verification/haz_four_site_cut.py \
    machine/pa194ha.instructions.json machine/pa194haz.instructions.json
  node comparison/verify-corpus.js
  python3 comparison/check-census.py
  node comparison/check-combined-corpus.js

All these checks were executed successfully. The Python build reproduces
the primary and A/D baseline checks, then HA and HAZ. JavaScript independently
resolves and verifies HAZ, and compares all machine/source artifacts with
Python's outputs. The separate four-site certificate imports neither the
compiler nor the symbolic simulator.

HA: 3650 source sites; 4750 source outcomes; 1,472,170 symbolic iterations.
HAZ: 3650 sites; 4751 outcomes; 1,472,644 symbolic iterations.
Maximum iterations per outcome: 497. Both complete blank startups: 58,122
physical transitions. Arithmetic-box rows are checked unchanged. Both
branches of every decrement are verified symbolically, including the new
positive branch that is unreachable by the independent source invariant.

The exact startup checks every one-cell and the zero exterior, at native
state 84, head -2, source site 25, logical registers (2,0,0,0,0,0,0,0,0),
and 26 spare one-valued registers. It does not establish infinite
nonhalting by simulation; that conclusion is calibrated to Con(PA) by proof.

COMPARISON

Snapshot: 1e407ae841e4666f932777fad977ba784ebbcfd5.
All 41 placed PA/docs packets and all five current incoming archives were
inspected. The census covers direct .tm files and complete numeric
five-column binary tables in .tm/.txt/.csv/.tsv archive members.

Prior corpus: 3,597 recognized one-halt table occurrences, 666 byte forms.
664 have a spanning root and form 476 action-graph classes. The 194-state
subset has 261 occurrences, 51 byte forms, and 28 graph classes, including
auxiliary and rejected tables. The extra four-state zero-halt-target fixture
is retained but excluded; six- and nine-state diagnostic controls have no
spanning root. None is a claimed small PA consistency machine.

HA and HAZ match none of the 28 prior classes under arbitrary state
renaming, any spanning root, global bit complement, and left/right
reflection. Comparisons use exact canonical strings. This is structural
novelty within the stated literal corpus, not semantic inequivalence or a
state-count lower bound. Unmaterialized parameterized search variants and
arbitrary source-code encodings are outside the exhaustive file census.

See comparison/design-status.json for the individual mechanisms and evidence
status, packet-ledger.json for all 41+5 packets, and combined-corpus-census.json
for all state counts and memberships. All 667 prior raw byte forms, including
the excluded fixture, are retained in raw-tables/ and raw-tables-extra/.

SEARCH

  node search/search.cjs machine/pa194haz.native.tm 74 8 384

The three rules are bounded literal-head detours, head displacement by two
cells, and a neighboring marker-bit representation. HAZ radius 8 / 384:
3,181,913 abstract contexts; 32,560 translated cases; 32,366 marker cases;
zero reductions. The radius-six run and HA runs are also negative. Earlier
V8 receipts and five additional auxiliary searches are included. These
negative results apply only to those sufficient contraction rules.

REPORT

report/pa194haz.tex is the main source. In report/, run:

  latexmk -pdf pa194haz.tex

or pdflatex -halt-on-error pa194haz.tex twice. The delivered mathematical
PDF was compiled from this source and visually checked. Its appendices
contain all 28 graph fingerprints, the complete 41-packet ledger, and all
194 transition rows (both read symbols, 388 actions).

PACKAGE MAP

  report/        Main LaTeX, PDF, and included tables/proof fragment.
  machine/       Native/dense tables, labels, resolved source, check receipts.
  build.py       Reconstructs and verifies HA and HAZ from frozen inputs.
  verification/  JavaScript port and independent source invariant checker.
  comparison/    Complete raw corpus, metadata, fixtures, executable census.
  search/        Exact bounded-search code, input tables, and run receipts.
  inputs/        Frozen primary table and AX grammar.
  vendor/        Unchanged compiler/runtime and PA196 source input.
  references/    Inherited mathematical proofs and scoped Lean context.
  licenses/      Preserved upstream licenses and new-material notice.
  provenance.json / SHA256SUMS   Source identities and file integrity.

Reference Lean files are context, not a standalone compiled HAZ Lean project.
The arithmetic-box oracle depends on the inherited fixed-engine lemmas.
The ordinary PA refutation translations are retained in references/calibration
and references/primary_packet/report for review.
