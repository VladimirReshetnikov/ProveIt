U213: a 213-state machine for the consistency of PA
===================================================

Preferred table: machine/u213.tm
Working states: 0..212. Initial state: 0. Separate halt: 213.
Alphabet: 0, 1. One two-way infinite tape, initially all 0. Initial head: 0.
Every transition writes one bit and moves one cell L or R.
Initialization is included. There are 213 working states and 426 transition rows.

Native labels are preserved in machine/u213.native.tm (halt 254).
machine/state_map.json gives the exact dense/native bijection.

Dense SHA-256:
0947330921e9ad0c26b2379aeb8a821108a1d42dab7c0eaa980fdcb29e5715c5
Native SHA-256:
38767d552131fb78e047225856c6759a9d45903c7c820bd0f06e071af07053b4
Source SHA-256:
2138b34bea88ab0fd469155229e6cb34ee185d45047d1b9994f4933be4d88896

The construction reduces the supplied primary U214 by one working state.
It exchanges two implication antecedents in the covering emitter, keeps
the 198-subtree source size, and allocates the result with the inherited
U217 return helper. A context repair reuses state 182 after a preceding 0.
Relative to the frozen U217 table, 64 retained rows change and four states
(native 500, 501, 502, 503) are deleted; no states are added.

Read paper/report.pdf for the complete argument and transition table;
paper/report.tex and included .tex sections are editable sources.

Proof status
------------
The exact source and physical reductions give an ordinary mathematical proof
formalizable in PA. Composing with the supplied U214 U/PA calibration gives:

  PA proves: not Halt(U213,blank) iff Con(U) iff Con(PA).

The new packet includes a 372-line schematic numerical proof of both full
axiom-bundle implications, exact source/CFG binding, 5,109 guarded
arbitrary-register primitive derivations, and a complete 95,726-step blank
trace to the calibrated seed. The source has 3,928 primitive occurrences.

No new Lean, Rocq or MM0 endpoint has been compiled for this table. The
separate formal K215 theorem concerns its own ZFC machine. The inherited
logical calibration is retained in its complete pinned archive. There is
no unconditional non-halting, absolute-minimality or priority claim here.

Reproduction
------------
Requires Python 3.10+ and only its standard library. Keep assertions enabled.

  python3 -B reproduce.py
  python3 -B reproduce.py --full
  python3 -B reproduce.py --full --report /chosen/path/replay.json

The default checks all supplied hashes, reconstructs the machine and source,
checks source binding and the numerical exchange proof, reruns the independent
table/local-entry/blank audit, checks the stored runtime inventory, and runs
the pinned U214 parent audit. It does not rederive the symbolic runtime.
The --full option additionally rederives all 5,109 cases on the exact U213 table
and compares the full saved case records and initialization trace.

The full runtime is an unbounded symbolic mathematical argument, using
induction on unary block lengths and finite lists. It is not a finite sample
of register values. Its implementation is ordinary Python, not a small
proof-assistant kernel. See the report for the precise trust boundary.

Rebuild the PDF with two pdflatex passes in paper/ after generating its
data with python3 -B code/build_document_data.py. Optional discovery scripts
under research/ require additional optimizer packages; final reproduction
does not use them. Rejected attempts are clearly identified there.

See NOTICE.txt, licenses/ and PROVENANCE.json for attribution and exact inputs.
