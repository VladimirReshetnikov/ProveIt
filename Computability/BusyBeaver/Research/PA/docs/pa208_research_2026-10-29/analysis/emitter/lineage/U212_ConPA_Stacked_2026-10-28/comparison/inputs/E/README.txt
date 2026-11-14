U213: REDUCING THE PRIMARY U214 MACHINE FOR CON(PA)
28 October 2026

RESULT

The primary machine is machine/u213.tm: 213 working states, two symbols,
426 transitions, and a separate halt label 213. Initialization from the
all-zero tape is included. The head starts at coordinate zero in state zero
on a tape indexed by the integers. Every transition moves one cell L or R.

The native table is machine/u213.native.tm, with sparse state identifiers
and halt label 254. Use machine/state_map.json to translate labels. The
proofs use native labels. All 213 working states are graph-reachable; this
does not assert that the blank run visits them all.

The new machine is mathematically shown equivalent to the exact primary
U214 retained in inputs/. Composing with that construction's explicitly
retained U214/U218/U222 and unary-theory calibration gives the same
PA-provable non-halting <-> Con(U) <-> Con(PA) endpoint. This archive contains
mathematical arguments and executable ordinary-Python certificates, not a
newly compiled Lean, Rocq, MM0, or exported PA proof of the entire endpoint.
It does not establish unconditional consistency, unconditional non-halting,
minimality, or discovery priority.

READ FIRST

paper/report.pdf         Complete research report and dense transition table.
paper/report.tex         Editable LaTeX source.
proofs/fold213.tex        Detailed predecessor-written-one state-fold proof.
machine/summary.json     Exact machine convention, counts, and key digests.

WHAT CHANGED

1. Reassociate the same 28 closed macros in source interval [2885,3659).
   All 3,928 opcode/operand pairs and all guarded ordinal destinations stay
   identical. Exactly 774 addresses change; the source still has 198 distinct
   subtrees. The fixed recipe is in inputs/source_recipe.json.

2. Use the new allocation, recorded as a 70-row patch from the original U214
   to inputs/reallocated214.native.tm. At the zero-tagged entry, native
   101/read0 selects existing decoder182, preserving state150's other roles.
   This is a context-specific binding, not a global modification of150.

3. Delete native167 and redirect native158/read1 to native172. Every entry
   into167 has a one immediately to its left. Under this invariant, the
   retained path matches one old step on read1 and two old steps with six
   steps on read0, preserving the entire tape and final head/state.

REPRODUCTION (OFFLINE; PYTHON 3.10+; STANDARD LIBRARY ONLY)

From this directory:

    python3 -B reproduce.py

This verifies the checksum manifest, reconstructs the exact source and both
tables without an optimizer, checks source/control-flow correspondence,
reruns two independently implemented fold checks and the repaired selector
check, audits recorded proof reuse/coverage, and independently replays the
95,714-step blank initialization. It checks that the inherited runtime
wrapper, naming map, symbolic checker and helper are byte-identical to the
included primary U214 baseline. It audits saved universal case records;
it does not regenerate all case derivations in this default mode.

To derive every final arbitrary-register case anew, without proof reuse:

    python3 -B reproduce.py --full --report /chosen/path/u213-replay.json

To additionally run the entire retained U214 reproduction, including its
companion machine's cases:

    python3 -B reproduce.py --full --parent-full --report /chosen/path/all.json

The --full route is slower. The universal cases quantify over arbitrary
natural register values and gap and an arbitrary nonempty finite spare list;
they are not finite tests of small values. Unary and list inductions justify
the acceleration rules. Temporary products are removed after reproduction.

To rebuild the PDF, from paper/ run twice:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex

The LaTeX source uses standard TeX Live packages listed in its preamble.

VERIFICATION COMPLETED FOR THIS DELIVERY

- All 5,109 guarded runtime obligations discharged for the final table.
- 4,194 previously completed cases transported through unchanged literal
  dependencies; 915 cases freshly derived (35 affected and 880 missing).
- All four list-traversal schemas rederived.
- Two independent local fold checkers, each checking 6,832 admissible
  radius-two frames and rejecting five semantic negative controls.
- Repaired selector182: all 16 admissible radius-two frames and three
  semantic negative controls.
- Exact source opcodes, operands, guarded ordinal successors, all binary
  successor counters, and no-stray-suffix conditions checked.
- Entire blank initialization independently replayed; final whole-tape
  root frame is identical to primary U214's calibrated frame. It has logical
  registers (4,0,0,0,0,0,0,0,0), gap1, and forty spares each equal to1.
- Primary U214's 5,109 symbolic cases were also freshly regenerated and
  compared to its archived records. Its reconstruction/proof audit, including
  its inherited U218 audit, completed. The separate all-cases companion U217
  rerun was interrupted and is not represented as a completed full-parent run.

CERTIFICATE LAYOUT

evidence/u213/             Final runtime summary, cases, startup and transfer.
evidence/u214_fresh_runtime/ Fresh primary U214 runtime derivations and seed.
evidence/                 Local/source/selector and independent audit receipts.
code/                     Standalone construction and checking scripts.
inputs/                   Exact baseline ZIP, unary-theory ZIP and fixed recipes.
licenses/                 Retained upstream license and provenance notices.
research/                 Search notes, negative results and rejected allocation.

IMPORTANT NEGATIVE CONTROL

research/rejected_allocation/rejected213.native.tm is NOT the final machine.
It uses the incorrect native101/read0 target150. Its universal check failed
at ordinal3256 (CI1) after4,229 completed cases. A concrete admissible
all-zero-primary frame with spare[0] returns the wrong result after530 steps.
The corrected target is182. The failed allocation's overall contract remains
rejected; only its individually completed proofs with unchanged dependencies
are reused. The initial allocator receipt is historical discovery evidence,
not a final correctness certificate.

The local167-to172 fold was valid even for that rejected pair. This example
shows why a correct local fold must still be paired with a valid compilation.

EXACT FINAL IDENTITIES (SHA-256)

Dense table:
9ed6f7bfa9f7988821bfe33e56eb3656dd2bc7d4f9b6951b6b23653b2936343a

Native table:
536872ebb6247342bdfd9fd0f50e71def3733e9514ae43971edcc7bc7beddd6c

Reassociated source:
f746fd0a238449ddb81d1cfb2be93d823d26f54fcc5296c680a28e5f02587af0

Corrected 214-state intermediate:
fdbfe27d27998952e957471ed5efc920ea8a2605fb9abf8c913dab6d6bb0b771

Every packaged file except SHA256SUMS itself is listed in SHA256SUMS.
See PROVENANCE.txt for source pins and the report bibliography for URLs.
