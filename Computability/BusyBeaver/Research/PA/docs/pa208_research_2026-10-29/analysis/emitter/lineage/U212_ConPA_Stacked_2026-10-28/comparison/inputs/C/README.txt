U213: REDUCING THE PRIMARY U214 MACHINE BELOW 214 STATES
28 October 2026

RESULT

machine/u213.tm is an explicit 213-working-state, two-symbol, single-tape
Turing machine, including its blank-tape initializer. It is obtained from
the supplied primary U214 construction by source reassociation, compatible
physical state reuse, an essential arithmetic-entrance correction, and a
one-state local fold. The full paper is paper/report.pdf; editable LaTeX is
paper/report.tex with included sections under proofs/ and the complete
dense transition table in paper/transition_table.tex.

The mathematical result is a PA-formalizable equivalence of blank-input
halting with the exact supplied U214 table. Composing it with the retained
U214 / Theory U calibration gives

  PA proves: not Halt(U213, blank) <-> Con(U) <-> Con(PA).

The direct literal U213/U214 reduction does not assume consistency or
depend on the logical soundness of the inherited calibration. The final
Con(PA) statement uses that calibration, whose exact original artifacts
are included. No newly compiled Lean, Rocq, MM0, or exported PA derivation
of the complete endpoint is claimed. This package provides mathematical
proofs, exact finite certificates, and executable symbolic verification.
It does not prove unconditional nonhalting or minimum possible state size.

MACHINE CONVENTIONS

  Working states: 0 through 212 inclusive.
  Halt label:     213, a separate nonworking state with no transition rows.
  Symbols:        0 and 1; blank is 0.
  Tape:           one tape indexed by all integers; initially all zero.
  Start:          state 0, head coordinate 0.
  Moves:          L or R on every transition; no stationary moves.
  Row format:     current_state read_symbol write_symbol direction next_state
  Row count:      426, exactly two rows for every working state.

machine/u213.native.tm is the identical machine with inherited native
state labels (native halt 254, native dispatcher 84). machine/state_map.json
is its checked bijection to the dense table. A native label such as 214
is an ordinary label and must not be confused with the working-state count.
All 213 working states are reachable in the transition graph; that census
does not assert that every state is visited on the blank run.

REPRODUCE OFFLINE

Use Python 3.10 or later, with its standard library. No network, optimizer,
external solver, or proof assistant is needed. Run from this directory:

  python3 -B reproduce.py

This checks the SHA256SUMS manifest, reconstructs the source and both tables,
checks the state bijection, resolves the complete source control graph in
two independent ways, replays both local fold checks and their mutation
controls, checks the repaired arithmetic entrance, runs two independent
blank-start simulators, and audits the saved symbolic-case coverage.

  python3 -B reproduce.py --full --report /tmp/u213-replay.json

This additionally reconstructs all 5,109 arbitrary-natural symbolic runtime
derivations and compares every resulting case record with its saved record.
The full portable replay took about 100 seconds in the preparation
environment; time depends on the machine. The finite checks take about
two seconds. The saved full replay ran before the final manifest was
sealed; the default finite replay additionally checks the final sealed
package. The release checks include a fresh replay from the finished ZIP.

  python3 -B reproduce.py --full --parent

This also unpacks and fully replays the exact supplied U214 archive,
including its 5,109 primary and 5,060 companion cases. Allow several
additional minutes. It does not fetch or substitute a newer parent.

Temporary work is removed by default. --report PATH retains the final JSON
receipt; --work DIRECTORY retains reconstruction and verification outputs.
Choose output paths outside this release directory to preserve its sealed
manifest. Do not use Python -O: executable proof checks must remain active.
reproduce.py is the supported entrypoint. The two hash-pinned inherited
runtime helpers are imported library modules; their historical demonstration
main blocks are not portable entrypoints and are not invoked by the replay.

To rebuild the report, with a standard TeX Live installation:

  cd paper
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Use a separate copy for rebuilding: PDF timestamps or TeX versions can change
its digest, and auxiliary files are not part of the sealed original package.

WHAT CHANGED

The accepted source retains all 3,928 primitive operations and their operands,
all 5,109 guarded outcomes, the same 198 distinct subtrees, and exactly the
same 28-token formula-constructor word. Only the source addresses of the
774-instruction covering emitter are reassociated. Its complete control flow
is identical after identifying instructions by ordinal, for every natural
register vector. No alternate logical schema or stronger theory is used.

A fixed 70-row reallocation produces the repaired 214-state intermediate.
It incorporates contextual-return ideas from the K215 constructions. The
required native row 204/0 is (0,R,182), not the rejected target 150.

Finally, native 167 has a unique incoming edge, 214/1, which writes 1 and
moves right. The preceding one lets existing native 172 implement the same
interface. Redirect 214/1 from 167 to 172, then delete both rows of 167.
The unequal-length matching paths preserve the entire tape and head and
have no internal halt. This last fold preserves halting on every common
initial tape. Its time bound t <= s <= 3t concerns this repaired intermediate
and U213, not the original U214 source layout.

VERIFICATION SCOPE AND RECEIPTS

  - All 5,109 guarded primitive contracts freshly rederived.
  - Every one of the 426 literal transition rows covered.
  - 1,368,534 symbolic inference applications in the successful case records.
  - Arbitrary natural primary values and gap, arbitrary first spare value,
    arbitrary finite remaining spare list, and the entire zero exterior.
  - Two local fold checkers: four opaque-exterior bit cases and 6,832
    admissible radius-two frames; 33 deliberately damaged controls rejected.
  - Two independent initializers agree on all 95,752 literal transitions
    and the exact calibrated root frame, including the zero exterior.
  - Source/control-flow, repaired-entry, native/dense, and parent bindings
    checked independently of the physical allocation recipe.

The runtime cases are universal contracts justified by induction on unary
lengths and finite lists; they are not simulations at 5,109 sampled input
values. Their saved JSON records contain outcomes, duration/displacement
formulas, coverage, and rule counts, not the full symbolic traces. --full
reconstructs the derivations using the literal table and induction rules.
The mathematical proof and the remaining proof-assistant boundary are
explained in the report.

FILES

  machine/    Final dense/native tables, source, state map, and summary.
  paper/      Main LaTeX report, compiled PDF, complete dense table appendix.
  proofs/     Source bisimulation, required repair/startup, and local fold.
  code/       Portable construction and independent/ inherited checkers.
  inputs/     Exact original U214 and Theory U archives, pinned source and
              machine inputs, frozen reconstruction recipes, provenance.
  evidence/   Per-case symbolic result records, startup trace, independent
              certificates, original-parent replay and portable replay logs.
  research/   Clearly separated rejected table and source-only further lead.
  licenses/   Retained upstream licenses, notices, and source pins.
  NOTICE.txt  Scope of attribution and new material.
  SHA256SUMS  Integrity manifest for all other delivered files.

EXACT FINAL IDENTITIES (SHA-256)

Dense table, machine/u213.tm:
c49b741c82bb2cf4616e127d67efc507125cd150b44e59051d9f2dda1c6622cd

Native table, machine/u213.native.tm:
2fb6a1c335686c0cd142dc61a86893d4ffa4cef12df592a7aab019ce0ea6d0a8

Source, machine/sites.json:
ba8888603313fa6a4ad40889a364b6b520d1516a6148bf37ffe364ca9c194658

The original incoming directory is pinned at ProveIt commit
24503cb019c7509ea229e80ef9b7a11a1501203c. Full download identities and URLs
are in inputs/provenance.json and the report bibliography.
