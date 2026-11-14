U213: a 213-state Turing machine for Con(PA)
==========================================
Research prepared for Vladimir Reshetnikov, 28 October 2026.

RESULT
------
machine/u213.tm is a complete binary, single-tape Turing machine with
213 working states (0 through 212), separate halt label 213, and 426
transition rows. It starts in state 0 at coordinate 0 on an entirely
zero, two-way infinite tape. Each transition moves one cell L or R.
Blank initialization is included. This is one working state below U214.

With the explicitly retained U214 numerical-calculus calibration and
the unary-power-cover interpretation arguments, the report proves

  PA |- not Halt(U213, blank) <-> Con(U) <-> Con(PA).

This is a mathematical proof formalizable in PA, accompanied by exact
executable verification. It is not a newly compiled Lean, Rocq, MM0,
or exported PA endpoint certificate. The inherited fixed K215/ZFC
endpoint is not used as a certificate for this changed PA machine.
No unconditional nonhalting, absolute minimality, or global priority
claim is made.

WHAT CHANGED
------------
1. Copy U214's exact 774-primitive role-a covering emitter into the
   direct-transfer ST215 source. The result has 197 distinct subtrees
   and 3,909 primitives, versus U214's 198 subtrees and 3,928 primitives.
2. Correct a context-sensitive allocation: native row 146/read 0 must
   enter existing state 182, not state 150. The known preceding zero
   makes the reuse exact; its local proof needs no additional state.
3. Redirect native row 34/read 0 from state 50 to state 75 and remove
   state 50, shortening the origin detector from eight zeros to seven.
   This is justified by the complete source-specific runtime proof,
   not by a maximum-zero-run heuristic.

The uncorrected raw 214-state allocation is retained only as an explicitly
rejected construction input for the contextual-entry certificate.

VERIFICATION
------------
All 5,084 arbitrary-natural primitive cases pass, including both branches
of all 1,175 decrements. The proof uses complete tapes with header distance
56+g for arbitrary natural g, all nine independent register values, and
an arbitrary nonempty finite spare list. It contains 1,277,411 symbolic
inference steps and covers every one of the 426 literal rows. Every source
primitive has positive literal duration; the minimum constant is 5 steps.
These are universal unary/list induction derivations, not small-input tests.

The exact blank run reaches native dispatcher 84 after 48,140 transitions:
head -2, header 54, source ordinal 136, PC 001100110101010, registers
(N,T,W,A,D,H,X,Y,L)=(1,0,13,0,0,1,0,0,1), 43 spare registers equal to 1,
120 one-cells, and zero exterior. This is an interior AX frame, not a clean
initial source root and not the original ST215 startup.

It matches 141 source steps from ordinal 106 with registers
(1,0,4,0,0,1,0,0,1). A new all-natural suffix lemma gives nine explicit
theorem heads above opaque numerical tail 4. The two actual field reads
consume the residual pointer, yielding a=0,b=2,c=0 and empty pointer.
The scheduler's exact conservative credit from candidate 1 is 2, so a
permanent margin of seven theorem heads protects the arbitrary tail.

Exact source/DAG audits jointly bind every one of the 3,909 primitives:
127 constructor/read calls, 5 gate calls, 15 command-exterior calls, and
5 primitive control instructions. The reentry certificate checks both
opaque-exterior blocks, all 6,864 admissible local induction frames, and
rejects three deliberately corrupted controls.

START HERE
----------
  paper/report.pdf                  Full 22-page report and complete table.
  paper/report.tex                  Editable main LaTeX source.
  paper/transition_table.tex         Complete generated table appendix.
  proofs/*.tex                      New source, compiler, runtime-entry,
                                    startup, credit, and provenance sections.
  machine/u213.tm                   Primary dense transition table.
  machine/u213.native.tm            Same machine with inherited labels.
  machine/state_map.json            Checked state-number bijection.
  machine/sites.json                Exact 197-subtree source.
  machine/summary.json              Machine counts and hashes.
  inputs/table_recipe.json          Frozen 73-row patch from native U218.
  code/                            Portable builders and proof auditors.
  evidence/                        Exact runtime, source, startup, and
                                    independent-review receipts.
  research/                        Limited-search and rejected-route records.
  inputs/U214_ConPA_Reduction_2026-10-28.zip
                                    Exact U214 predecessor, including its
                                    embedded dependencies and proofs.
  inputs/pa_unary_power_cover.zip    Exact supplied theory U report and code.
  references/ProgLibPerm.v          Named inherited arithmetic lemmas.
  references/ST215/                 Inherited compiler/credit arguments
                                    and attribution records.

Each transition line is:
  state  read_bit  write_bit  L_or_R  next_state
The halt label has no outgoing rows. Native halt is 254; dense halt is 213.
Numeric native labels are labels, not state counts.

REPRODUCE OFFLINE
----------------
Use Python 3.10 or later, standard library only. From this directory:

  python3 -B reproduce.py
  python3 -B reproduce.py --full
  python3 -B reproduce.py --full --report /chosen/path/replay.json

The first command checks the manifest, all exact reconstructions and
source bindings, both full source CFG resolvers, the local reentry proof,
the exact blank startup, saved universal proof coverage, retained checker
origin, and the predecessor's finite audit. --full additionally rederives
all 5,084 universal primitive cases and compares every derivation with
the saved data. It requires no network, solver, optimizer, or proof assistant.
Assertions must remain enabled; do not use -O or PYTHONOPTIMIZE.

Temporary work is removed; only an explicitly chosen --report persists.
Runtime varies by hardware. The new symbolic replay took about 94 seconds
in one preparation run. Finite audits take several additional seconds.
These timing observations are not performance guarantees.

To rebuild the PDF, run twice from paper/:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF bytes may vary with TeX versions and timestamps. Editing release files
invalidates SHA256SUMS; retain an untouched extraction for verification.

EXACT IDENTITIES
----------------
Dense U213 SHA-256:
3fdd869eac6d2fc666da209b9d620de91ca963bd8dab21309d1093f74a1ec3f0
Native U213 SHA-256:
bb4f5ac12b29d07d1080109af9bb564e9e11a4783efc48cd73b8f826789d01f7
Source SHA-256:
7b6539dc67b66ff73f22554018d7af5985d85574460a73fea5f025103c523d00

PROVENANCE AND LIMITS
--------------------
The source snapshot is ProveIt commit
24503cb019c7509ea229e80ef9b7a11a1501203c. PROVENANCE.json records the exact
incoming archive and source hashes. The predecessor preserves the supplied
U/W/PA mathematical interpretations. The direct-transfer source and source
framework retain the third-party notices and licenses in licenses/.

Independent reviews in this packet mean separate assistant passes within
this collaboration, not external human review. The finite checkers do not
silently replace the named all-natural arithmetic lemmas or the theory U
interpretation. The report includes Further research questions.

The six-zero 212-state attempt was not certified: its first symbolic case
did not close within the proof-construction limit. No literal counterexample
was recorded for it. Restricted allocation and local-fold searches found
no further saving; this is not a lower bound on possible machines.
