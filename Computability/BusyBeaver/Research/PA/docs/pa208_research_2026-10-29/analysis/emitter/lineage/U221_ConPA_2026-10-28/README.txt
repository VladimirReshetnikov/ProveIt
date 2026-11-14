U221: A 221-STATE BINARY TURING MACHINE FOR Con(PA)
28 October 2026

RESULT

This package reduces the supplied primary U222 candidate to 221 working
states, 442 transition rows, two symbols, one tape and one head. Initialization
is included. The dense table starts in state 0 on an all-zero tape, moves only
L/R, and has a separate halt label 221, excluded from the working-state count.

The new elementary mathematical theorem is

  PA |- Halt(U221, blank) <-> Halt(U222, blank).

Composing it with the supplied U222 mathematical correctness and uniform
interpretation arguments gives

  PA |- not Halt(U221, blank) <-> Con(U) <-> Con(PA).

The source-independent reduction preserves the entire tape and head position
at every step and exact halting time. It holds on EVERY binary initial tape
from state 0, not only the blank tape. It does not establish unconditional
non-halting or consistency. No global minimality is claimed.

THE ENTIRE NATIVE-TABLE CHANGE

  Replace: 112 1 1 R 200
  By:      112 1 1 R 209
  Delete:  200 0 0 R 157
  Delete:  200 1 1 R 119

All other rows are unchanged. The complete original table has only the
following incoming edges to 112 and 200:

  172 0 0 L 112
  112 1 1 R 200

Thus state 112 always has zero immediately to its right, and state 200 is
always entered reading zero. Its zero row agrees with state 209's zero row.
The quotient map 200 -> 209 therefore commutes with every reachable step.
An exhaustive independent check verifies 7,072 admissible five-cell local
frames; all 11 mutations of proof premises are rejected. The full inherited
runtime checker also passes all 5,060 arbitrary-register cases, and literal
blank initialization still takes exactly 95,714 steps.

The accepted K215 predecessor had a second entry into 112 from state 215/read 1.
U222 source recompilation removes that entry. The smaller theory emitter
therefore exposes a new conditional merge in the inherited decoder.

START HERE

  paper/report.pdf             Complete mathematical report and transition table
  paper/report.tex             Editable TeX source
  machine/u221.tm              Dense table: working 0..220, halt 221
  machine/u221.native.tm       Proof-friendly native labels, halt 254
  machine/state_map.json       Exact native/dense bijection
  machine/machine_summary.json Exact counts and byte identities
  machine/sites.json          Source retained byte-for-byte from U222
  code/                       Deterministic builders and independent checkers
  evidence/                   Proof certificates, complete runtime case records
  experimental/source202/      Smaller equivalent source, separately audited;
                              no additional physical machine claim
  inputs/U222_ConU_2026-10-28.zip
                              Exact unmodified parent with all theory dependencies
  PROVENANCE.json             Pinned input archive identities and review scope
  NOTICE.txt                  New-work scope and inherited attribution
  SHA256SUMS                  Manifest of every packaged file except itself

PROOF STATUS

The reduction uses only a finite invariant and induction on run length. Its
machine-equivalence theorem is independent of the old source compiler or
Theory U's arithmetic interpretation. The Con(PA) endpoint imports those
U222 correctness arguments explicitly. This release contains an ordinary
mathematical proof and executable certificates, not a newly compiled MM0,
Rocq, or Lean kernel proof of the final endpoint. The earlier K215 ZFC theorem
does not automatically certify U222 or U221.

OFFLINE REPRODUCTION

Python 3.10+ and its standard library suffice. No network or solver is used.

  python3 -B reproduce.py
  python3 -B reproduce.py --full --report replay.json

The first command checks all release hashes, rebuilds the tables and source,
reruns both independent reduction certificates and negative controls, extracts
and re-audits the exact parent archive, and independently replays startup.
It also checks the exact supplementary 202-node source reconstruction and CFG.
The --full command additionally rederives all 5,060 symbolic cases and compares
the exact deterministic runtime records. It normally takes a few minutes.
Generated work is temporary except for the explicitly requested report path.
Running with Python -O is not supported by the inherited symbolic checker.

TABLE FORMAT

The first line is '#! start 0'. Each remaining row has five fields:

  state read_symbol write_symbol direction next_state

There are no outgoing rows for halt. Both symbols have a row at every working
state. The largest native label is not the state count; use the dense table
for a conventional contiguous enumeration.

BUILD THE PAPER

  python3 -B code/build_paper_data.py
  cd paper
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF bytes may depend on TeX versions and timestamps. Regenerating any published
file changes the manifest identity; keep an untouched copy for hash checking.

FURTHER WORK

The report includes scoped negative results and further research questions.
Any additional exploratory source recipes are explicitly identified as such;
source DAG counts must not be interpreted as physical Turing-machine counts.
