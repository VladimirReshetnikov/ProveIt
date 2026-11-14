PA194AX11QH5 -- COMPLETE RESEARCH PACKAGE
14 November 2026 (Pacific time)

RESULT

This package supplies a new 194-working-state binary, one-tape, blank-start
Turing machine with the ordinary mathematical equivalence

  PA proves: not Halt_blank(PA194AX11QH5) <-> Con(PA).

No verified machine below 194 states was obtained. This is the requested
alternative construction at 194, combining the eleven-entry AX protocol
with coefficient-five formula coding, exchanged quantifier distribution,
no-push MP and cache-only Shift. Its recurring command language has four AX
fields, and the compiled refutation ends with Pop rather than Shift.

The PA calibration is inherited and reviewed; the changed command proof is
new. Two executable physical symbolic checkers, a source-splice certificate,
independent command identities, emitter binding, and full blank startup
support the construction. They are not a newly exported end-to-end Lean,
Rocq or iPRA theorem. No global lower bound or global priority claim is made.

START HERE

  report/pa194_ax11qh5_report.pdf    Complete report, proof and transition table
  report/pa194_ax11qh5_report.tex    Main compilable TeX source
  machine/machine.tm               Authoritative dense literal table
  RESULTS.json                    Consolidated machine-readable evidence
  PROVENANCE.json                 Source snapshot and attribution boundaries

MACHINE CONVENTION

Working controls: 0 through 193. Start: 0. External halt: 194 (no rows).
Tape: cells indexed by all integers, initially all zero. Initial head: 0.
Alphabet: {0,1}. One tape. Every action writes a bit and moves L or R.
Exactly 388 rows, each: state read write direction next.

The dense table SHA-256 is:
f7f52501055ff4fe47aab51acc6536adf3823afca4016a670c67b2c592ed4b02

Native labels use start 74 and halt 254. They are not state counts. The exact
native-to-dense bijection is machine/labels.json. Graph reachability from the
start covers every control, without asserting that the blank run visits all
controls. The literal allocation is 135 fixed + 67 AX readers - 8 folds.

REPRODUCE THE SUCCESSFUL CONSTRUCTION

Requirements: Python 3.10 or newer; standard library only; assertions enabled.
Run from this directory (do not use Python's -O option):

  python3 -B verify.py

This checks file integrity, rebuilds the source and machine in a fresh
temporary directory, compares all core files byte-for-byte, replays the
primary and independent universal physical contracts, checks complete blank
initialization, source relocation, inherited emitter binding, symbolic
command identities, integer stack regressions, and all 82 reference graphs.
The full replay can take several minutes. It does not modify frozen evidence.

For an integrity, construction, startup, source, command and novelty check
without the two expensive universal physical replays:

  python3 -B verify.py --quick

An optional receipt can be written outside the package:

  python3 -B verify.py --output /path/to/fresh_receipt.json

Individually useful commands:

  python3 -B construction/build.py --output /path/to/fresh_machine
  python3 -B verification/check_physical.py /path/to/fresh_machine
  python3 -B comparison/check_novelty.py machine/machine.tm --recompute

The builder's --quick option skips its universal physical replay but still
builds the table, resolves the source, checks all folds, and checks startup.

REPORT

The PDF includes the complete new protocol proof, logical dependency chain,
physical invariants, every transition, a comparison by architecture, a ledger
of all 72 supplied deliveries, and exact scopes of unsuccessful reductions.

With an ordinary TeX Live installation:

  cd report
  pdflatex -interaction=nonstopmode -halt-on-error pa 194_ax 11 qh 5_report.tex
  pdflatex -interaction=nonstopmode -halt-on-error pa 194_ax 11 qh 5_report.tex

All input TeX fragments are in that directory. Files under references/ are
preserved prior proof texts and source excerpts; they are dependencies and
historical references, not each an independently compilable main document.

COMPARISON SCOPE

Pinned ProveIt commit:
  4be5c6e3a10292a7466f5d3687e3b39615ff049b

The two requested PA/incoming locations contain 61 filed and11 incoming
deliveries:72 packets. The fresh census covers 21,051 tracked paths,3,663
recognized literal-table occurrences and 82 full 194-state control graphs.
The new table has no match under state renaming, every graph-spanning root,
tape reflection, bit complementation and ignored terminal-edge actions.
The enlarged symmetry comparison is a corpus identity test; symbol exchange
alone does not preserve the all-zero blank convention.

The scanner recognizes numeric five-column tables and textual/five-column
JSON arrays, including nested archives. It does not execute arbitrary
generators or interpret arbitrary dictionary encodings, diagrams or prose.
Historical evidence labels attribute their supplied reports. All principal
delivered literal tables are covered, but every historical mathematical
calibration was not independently rebuilt here.

comparison/ contains full occurrence/class CSV and JSON files, exact hashes,
the 72-packet ledger, all 82 literal reference representatives, and a portable
scanner. Reproduce the full census using a local copy of the pinned repo:

  python3 -B comparison/audit_current.py /path/to/ProveIt \
    --revision 4 be 5 c 6 e 3 a 10292 a 7466 f 5 d 3687 e 3 b 39615 ff 049 b \
    --output /path/to/fresh_census

NEGATIVE SEARCHES

research/finite_searches/ and research/grammar_search/ retain exact inputs,
source code, logs, seeds, counts, limits and reproduction instructions.
The former includes the four-edit Runtime193 bootstrap search, every-pair
bounded local quotients, one-helper-row variants, and an exact 93-step
rejection of the parity-scheduler/runtime-quotient combination. The latter
contains four sampled AX association searches with compatible fold scoring.
No experiment proves that 194 is minimal. The 1,870 bounded startup runs
remain unresolved beyond their cutoffs. Search tools require a C++17 compiler.

ATTRIBUTION AND TRUST BOUNDARY

The exact direct parent is secondary_qh 5 in the supplied AX11 incoming ZIP.
Only native row(2066,1) changes:0 L 302 becomes 1 R 19. This replaces the AX return
by the existing stack push and falls through the full MP reader, changing
the recurring protocol. Fixed nodes and all other physical rows are retained.

The original numerical calculus, PA calibration, physical engines, compiler
and symbolic runtimes are inherited from the ProveIt research lineage.
Their notices and licenses are preserved. PROVENANCE.json, references/
PROVENANCE.json and the local reference closures identify the dependencies. Some historical census receipts
retain their original scratch paths as provenance; runnable tools use the
portable relative paths and repository/archive-member locators instead.

The mathematical theorem is unconditional as a PA-provability statement;
it does not assume Con(PA) in its proof. Inferring actual nonhalting uses
Con(PA), exactly as specified. No finite blank simulation can establish
actual nonhalting, and the supplied checks make no such claim.

SHA 256 SUMS lists the delivered files except itself. All finite evidence is
readable separately, and the report states which layer each check supports.
