PA194QN5 and PA194QN6: comparison, construction, and reduction research
=====================================================================

READ FIRST
No valid machine below 194 working states was established. This archive
delivers the requested same-size fallback: PA194QN5, plus PA194QN6 as a
companion. The report is report/pa194qn_report.pdf; its complete LaTeX source
and generated includes are in the same directory. Section 1 states the
ordinary mathematical claim and the counting convention. Appendices print
the complete principal transition table and the 66-delivery comparison.

The repository comparison is pinned to
  2337ce611a26e308697ccbddb2a1636f989f01c3
of https://github.com/VladimirReshetnikov/ProveIt . It covers the 61 filed
PA packets and five incoming archives at that revision. Later additions to
main are outside the scope. All 576 recognized component fingerprints have frozen
representatives; 76 are spanning one-halt 194-state classes. Some of those
tables are auxiliary or rejected experiments, not consistency machines.

Principal machine: machines/PA194QN5/machine.tm
Companion machine: machines/PA194QN6/machine.tm
Each table has 194 working controls (0 through 193), start 0, terminal label
194, and 388 transitions. The tape alphabet is {0,1}, the blank is 0, the
tape is two-way infinite, and the head starts at coordinate 0. Each line is
current_state read_bit write_bit L_or_R next_state.

These machines combine the supplied Q quantifier-distribution exchange,
the no-push MP operation returning its conclusion in the visible top, the
original sum-based Shift halt test, and coefficient-5 or coefficient-6
formula constructors. The individual ideas are inherited. The new result
is the exact crossed construction and its source, table and proof bindings.

No machine below 194 is claimed. The ordinary mathematical PA equivalence
uses the explicitly included inherited numerical-calculus calibration and
the new composition argument in proof/proof_QN_radix.tex. Executable checks
do not constitute an end-to-end Lean/Rocq theorem or an iPRA equivalence.

Reproduction, Python 3.10+ (standard library only; no network):

    python3 -B reproduce.py --full

This writes all fresh generated files into a new temporary directory and
prints its location. To choose it, add --work /new/nonexistent/directory.
Full mode reruns every construction symbolic source contract and the separate
literal-tape checker, including derivation of four arithmetic list lemmas,
all arbitrary-register outcomes, and the entire blank initialization.

    python3 -B reproduce.py --quick

Quick mode still reconstructs the exact sources and tables, checks the input
hashes, all source relocation edges and multiplier bodies, free-algebra AX
effects, all simultaneous fold contexts, whole startup, and the independent
source/emitter parser. It also rechecks novelty against the frozen frontier,
reparsing the literal corpus representatives. It omits BOTH long universal
physical replays. The recorded full-component results are in
evidence/full_component_replay.json and evidence/independent/.
Do not run any checker with -O or PYTHONOPTIMIZE.

To check novelty separately:

    python3 -B comparison/check_novelty.py machines/PA194QN5/machine.tm machines/PA194QN6/machine.tm

This comparison allows any spanning root, arbitrary control renaming, tape
reflection and global bit exchange, and ignores terminal write/move effects.
Global bit exchange is a stronger structural screen; it is not asserted to
preserve the zero-blank execution. Both candidate match lists are empty.

The exact comparisons and negative-search evidence do not establish any
lower bound on all machines, or any worldwide priority claim.

The accepted dense SHA-256 identities are:
QN5 30d762c8192a21936511931f35f72888d7b8249128633a5c019435fdd173ad1f
QN6 72a35e528c1061f61e211d0bcf3a954859d2dbbcfd6b9f7846e4f970bb04e4e9

Package layout:
construction/       deterministic builder and frozen source/table inputs
verification/      independent source, formula and literal-tape verification
machines/          accepted tables, source JSON and construction receipts
evidence/          recorded independent verification outputs
proof/             new argument and attributed inherited proof fragments
comparison/        66-delivery ledger, 76-class frontier, 576 frozen tables
references/        additional attributed calibration sources and project status
research/physical/ bounded two-edit startup screen and explicit relay failure
research/threeway/ bounded local screen for a combined comparator/multiplier
report/            complete LaTeX report, generated tables, compiled PDF
licenses/          retained original notices
PROVENANCE.json    pinned repository snapshot and exact inherited input hashes
RESULTS.json       concise machine identities, counts, claim and limitations
SHA256SUMS         hashes of all released files except the manifest itself

The first checker uses retained generic arithmetic-block lemmas. The second
derives these list lemmas directly from the literal transition rows and does
not import the builder or its arithmetic-block oracle. Both check arbitrary
natural register values and arbitrary allowed spare lists/gap lengths, not
just finite sampled values. The exact 58,320-step blank startup compares all
nonzero tape cells; it is an initialization check, not evidence of nonhalting.

OPTIONAL NEGATIVE RESEARCH
The physical search has its own README and portable reproducer. Its full run
needs g++ with C++17 support in addition to Python; ordinary machine
reproduction does not run this search. From research/physical/:

    python3 -B reproduce.py --quick
    python3 -B reproduce.py --output /absolute/fresh/directory

The quick physical check replays the concrete relay counterexample and ray;
the full path also repeats the bounded two-edit search. The recorded 775
bounded representatives remain unresolved beyond the specified bounds.

BUILDING THE PDF
Use a TeX installation with pdflatex and the standard packages named in the
preamble. From report/:

    python3 -B generate_includes.py
    pdflatex -interaction=nonstopmode -halt-on-error pa194qn_report.tex
    pdflatex -interaction=nonstopmode -halt-on-error pa194qn_report.tex

The include generator reads the released tables and evidence. It never
reconstructs a transition table from prose. Rebuilding the PDF may change
its bytes because TeX embeds timestamps and document identifiers; the
accepted TM hashes above do not depend on the PDF renderer.

ATTRIBUTION AND PROOF STATUS
The original PA196 program and implementation ancestry are due to James
Chang and other authors credited in the retained source notices. Vladimir
Reshetnikov's ProveIt repository and its supplied research packets provide
the Q, no-push, radix, runtime193 and calibration ingredients. The new work
here is the exact QN5/QN6 composition, fresh source/table bindings and
verification, current-corpus comparison, and the documented additional
negative searches. The ordinary proof uses those inherited calibrations.
See NOTICE.txt, PROVENANCE.json, licenses/ and each research README.
