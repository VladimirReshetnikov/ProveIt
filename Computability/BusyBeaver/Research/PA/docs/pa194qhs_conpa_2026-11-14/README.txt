PA194QHS: A 194-STATE PA CONSISTENCY MACHINE
Research release prepared for Vladimir Reshetnikov, 14 November 2026

RESULT

No machine below 194 working states was established. This package gives
the requested fallback: a concrete, previously absent 194-state composition,
PA194QHS, with an ordinary mathematical proof formalizable in PA that

  not Halt(PA194QHS, blank) if and only if Con(PA).

The construction combines credited existing Q, H and S mechanisms. QHS
has the exchanged quantifier-distribution head, visible-result no-push MP,
and symmetric cache-only Shift. Relative to the nearest QH parent it removes
an entire restoration loop, with unbounded source-instruction savings.
There is no claim of a new logical principle, a state-count record, a
uniform literal-TM speedup, or a newly checked Lean/Rocq endpoint.

START HERE

report/pa194qhs.pdf          Full report, mathematical proof, comparison,
                            all transition rows, 66-packet ledger.
report/pa194qhs.tex          Complete LaTeX source (all inputs alongside).
machine/machine.tm          Dense literal table: start 0, halt 194, 388 rows.
machine/machine.native.tm   Native presentation: start 74, halt 254.
machine/labels.json         Exact dense-to-native conjugacy.
verify.py                  Self-contained machine and certificate verification.
comparison/                Complete corpus data, novelty audit and provenance.
search/                    Additional unsuccessful state-reduction searches.
PROVENANCE.json             Repository snapshot and incoming archive hashes.

MACHINE

194 working states, excluding terminal halt. Binary alphabet. One head on
a two-way infinite tape, initially all zero. Every transition writes a bit
and moves one cell left or right. Initial head position is zero.

Dense SHA-256:
3bf22abe66e327d63d1feacacda9cc6f1b6529d09ca779c10f22fa5ed3acd103

Native SHA-256:
f548197b33889b879d4dce83f6e9ef9322b8a21f0ca8864a566b3ca0c0aed518

Each table row is: state read_bit write_bit direction next_state.

REPRODUCE

Python 3.10+ and the standard library suffice. From this directory:

  python3 -B verify.py --output evidence/fresh_verification.json

This rebuilds the exact tables, checks all 32 simultaneous fold cases,
all 4,750 universal source outcomes, complete blank initialization, command
identities, source-block preservation, the finite exchange certificate,
novelty against the pinned corpus, and the independent literal-tape replay.
Do not use Python -O or PYTHONOPTIMIZE. The verifier rejects disabled
assertions. The optional --quick skips only the independent literal replay.

To rebuild the PDF, enter report/ and run twice:

  pdflatex -interaction=nonstopmode -halt-on-error pa194qhs.tex

The optional reduction-search replay requires a C++17 compiler; see
search/README.txt. None of those negative searches is a lower-bound proof.

COMPARISON

Pinned ProveIt revision:
2337ce611a26e308697ccbddb2a1636f989f01c3

The comparison covers 61 filed packets and 5 current incoming archives,
direct PA literal tables, and recursive nested archives. The census found
1,522 complete numeric table occurrences, 634 byte forms, 630 labeled
transition functions, 563 spanning action-graph classes, and 76 spanning
194-state classes. Input tables include rejected candidates and diagnostics.
Neither of the two 193-state cores has a valid blank-start calibration.

QHS has no graph match in that corpus, even after state renaming, arbitrary
spanning-root choice, tape reflection, and global bit interchange. This is
a relative corpus claim, not a global priority claim.

PROOF STATUS

The proof is an ordinary mathematical composition of the inherited
syntactic PA calibration and the new source/tape preservation argument.
The source preservation is valid for arbitrary incoming scratch; its exact
loop patterns and sole entry edge are independently checked. Literal
runtime contracts quantify over all natural register values, arbitrary
header gap, and arbitrary nonempty natural spare lists. Startup is checked
on the entire tape after 57,768 transitions.

Executable certificates are evidence for finite checks and universal
symbolic contracts through the documented loop lemmas. They are not an
end-to-end proof-assistant kernel theorem. The stronger machine-specific
iPRA internalization remains a separate repository project.

ATTRIBUTION

The source compiler, arithmetic engine, Q emitter, symmetric controller,
history-sensitive folding technique, independent runtime machinery, and
ordinary PA logical calibration are inherited and credited. See NOTICE.txt,
licenses/, references/, and evidence/inherited_files.json.

The final MANIFEST.json records every release file except itself.
