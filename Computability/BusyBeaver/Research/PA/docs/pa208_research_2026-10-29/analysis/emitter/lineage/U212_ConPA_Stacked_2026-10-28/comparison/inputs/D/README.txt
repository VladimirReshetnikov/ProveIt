U213: one state below the primary U214 machine for Con(PA)
========================================================
Research prepared for Vladimir Reshetnikov, 28 October 2026.

RESULT
------
machine/u213.tm is a complete deterministic binary, single-tape Turing
machine with 213 working states (0,...,212), separate halt label 213,
and 426 transition rows. It starts in state 0 at coordinate 0 on an
all-zero, two-way infinite tape. Every transition moves exactly L or R.
Initialization is part of the table.

One closed source reassociation preserves all 3,928 primitive instructions,
their operands, and every ordinal control-flow target. The source still
has 198 distinct subtrees. Contextual decoder allocation and repair of a
retained parent's child reference change 36 retained native transition
rows and delete native state 215. No state is added.

The exact literal table passes all 5,109 arbitrary-natural primitive cases,
including arbitrary gaps and nonempty finite spare-register lists. A
95,726-step blank start reaches the same calibrated seed as U214:
native state 84, head -8, gap 1, logical registers (4,0,0,0,0,0,0,0,0),
and forty spare registers all equal to one.

The mathematical reduction gives

  PA |- Halt(U213, blank) <-> Halt(U214, blank).

Composed with the explicitly inherited U214/U218/U222 numerical-calculus
calibration and unary-power-cover interpretation arguments, this gives

  PA |- not Halt(U213, blank) <-> Con(U) <-> Con(PA).

PROOF SCOPE
-----------
The package contains mathematical proofs formalizable in PA and executable
checks of the exact construction, source control flow, blank initialization,
and unbounded unary/list-inductive primitive simulations.

No newly compiled Lean, Rocq, MM0, or exported PA endpoint certificate is
claimed. The fixed K215 theorem for Con(ZFC) does not certify this changed
machine. No unconditional consistency or non-halting result, absolute
minimality claim, or discovery-priority claim is made. Separate audits
were implemented within this assistant research collaboration; they are
not external human review.

START HERE
----------
  paper/report.pdf               Main report, proofs, complete patch/table.
  paper/report.tex               Editable main LaTeX source.
  paper/transition_patch.tex     Every changed retained native row.
  paper/transition_table.tex     Full dense transition table.
  machine/u213.tm               Primary dense 213-state machine.
  machine/u213.native.tm        Same machine with inherited native labels.
  machine/sites.json            Exact reassociated register-program source.
  machine/state_map.json         Native-to-dense bijection, including halt.
  inputs/recipe213.json          Frozen source/table construction data.
  code/build213.py              Deterministic construction and prefix audit.
  code/audit213_independent.py   Independent source/table audit.
  evidence/u213/                Complete runtime cases and startup trace.
  evidence/predecessor/         This session's U214 full-replay receipt/log.
  research/                    Supplementary negation and rejected-detector work.
  inputs/U214_ConPA_Reduction_2026-10-28.zip
                                Exact supplied predecessor and dependencies.
  PROVENANCE.json               Pinned public input identities.
  SHA256SUMS                    Exact release-file checksums.

Table lines have the format

  state  read_symbol  write_symbol  direction  next_state

There are no outgoing rows for the halting label. Native halt is 254;
dense halt is 213. Native labels are names, not counts. The state map is
part of the checked construction.

REPRODUCE OFFLINE
----------------
Python 3.10 or later, standard library only. From this directory:

  python3 -B reproduce.py
  python3 -B reproduce.py --full
  python3 -B reproduce.py --full --report /chosen/path/replay.json

Default replay checks the release manifest; source and table reconstruction;
both exact source control-flow resolvers; literal decoder prefix bindings;
independent source/table audit; dense relabeling; saved runtime bindings and
case coverage; an independent literal startup replay; and the inherited
U214 construction/proof audit.

--full additionally rederives every one of the 5,109 U213 symbolic cases.
These quantify over arbitrary natural register values, gap, first spare,
and finite remaining spare list. They are not samples of small inputs.
Proof-construction limits do not bound the represented literal executions.

No network, optimizer, solver, or proof-assistant installation is needed.
The script refuses optimized Python execution (-O / PYTHONOPTIMIZE).
Temporary reconstruction files are removed automatically; only an explicitly
requested report is retained. Runtime depends on hardware.

The predecessor's --full replay was also rerun during construction; it
rederived 10,169 primary/companion cases and passed its inherited U218
audit. Its receipt is saved under evidence/predecessor. To rederive that
longer inherited replay again, extract the supplied input archive and run
its own reproduce.py --full.

REBUILD THE PDF
---------------
With a normal pdfLaTeX installation:

  cd paper
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Only PDF rebuilding needs TeX. The two table fragments are included by
report.tex. Rebuilt PDF bytes may vary with TeX versions and timestamps.
Editing release files invalidates the manifest; retain an untouched copy
for auditing.

EXACT IDENTITIES
----------------
Dense U213:
0300cc34a94e51b409214d3313e0a5d8bbc2974f7832ee13ff323d49a86c0fcd
Native U213:
94081dc08a8c47bd0cb5694e84333539126566106363259f62043d598c8d1bcc
Reassociated source:
91f1a7a6c80c4ccefe4cb30716b1631493951647fca0d97d57bb0ad5b21ee032

New material follows the project's MIT No Attribution terms. Inherited
notices and licenses remain in licenses/ and in the exact input archive.

RELEASE CHECK
-------------
The packaged full replay passed in 191.860 seconds on the construction host.
Its receipt and log are evidence/package_full_replay.json and .log.
It reconstructed every U213 symbolic case record exactly and passed the
inherited U214 audit. The final manifest was rechecked after adding the
replay receipt and final PDF quality record; therefore the manifest count
in the historical replay receipt precedes those additions.
