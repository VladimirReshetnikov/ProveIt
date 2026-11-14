U214: four states below the primary U218 Con(PA) machine
======================================================
Research prepared for Vladimir Reshetnikov, 28 October 2026.

PRIMARY RESULT
--------------
machine/u214.tm is a complete deterministic binary, single-tape Turing
machine with 214 working states (0,...,213), separate halt label 214, and
428 transition rows. It starts in state 0 at head coordinate 0 on an all-zero,
two-way infinite tape. Every transition moves one cell L or R. The table
includes blank initialization; no nonblank input is supplied.

A new assignment of matrix/output, source and test roles reduces the emitter
from 202 to 198 distinct source subtrees and compiles to a 215-state machine.
A guarded state fold then removes native state 156. The expanded source has
3,928 primitive occurrences: shorter source and fewer physical states are
different objectives.

Using the explicitly retained U218/U222 numerical-calculus calibration and
the unary-power-cover interpretation arguments, the paper proves

  PA |- not Halt(U214, blank) <-> Con(U) <-> Con(PA).

The new logical argument covers all selectors, including 0, 1 and coincident
source/output labels. Exact arithmetic macro bindings and all 3,154 exterior
primitives are checked. All 5,109 symbolic runtime cases pass. A literal
95,726-step blank start reaches the calibrated root with logical registers
(4,0,0,0,0,0,0,0,0), gap 1, and forty spare registers equal to one.

These are mathematical proofs formalizable in PA, with exact executable
verification. No newly compiled Lean, Rocq, MM0 or exported PA certificate
of the complete endpoint is claimed. The package makes no claim of
unconditional consistency, unconditional non-halting, absolute minimality,
or discovery priority. The inherited fixed K215 theorem concerns ZFC and
is not silently used to certify this changed PA machine.

DIRECT 217-STATE COMPANION
-------------------------
machine/u217_reentry.tm preserves U218's source exactly. In native labels,
it changes only the target of 172/read 0 from 112 to 134 and deletes state
112. A two-sided local convergence proof gives halting equivalence directly
with literal U218 on every initial tape. It also passes all 5,060 symbolic
cases and blank startup. It is included for its small proof change.

START HERE
----------
  paper/report.pdf                  Full report, proofs and primary table.
  paper/report.tex                  Editable main LaTeX source.
  paper/transition_table.tex         Complete primary table appendix.
  proofs/*.tex                      Source, logic and local proofs.
  machine/u214.tm                   Primary dense transition table.
  machine/u214.native.tm            Same table with inherited native labels.
  machine/u217_reentry.tm           Direct 217-state companion.
  machine/sites.json                Exact 198-subtree source.
  machine/*_state_map.json           Checked native/dense bijections.
  machine/summary.json               Counts and SHA-256 identities.
  inputs/source_recipe.json          Frozen source reconstruction.
  inputs/table_recipe.json           Frozen transition patch.
  inputs/role215.native.tm           Verified 215-state intermediate.
  evidence/u214/                    All 5,109 derivations and startup.
  evidence/u217/                    Companion runtime evidence.
  evidence/package_full_replay.json Full offline replay receipt.
  evidence/*fold*.json              Independent local certificates.
  inputs/U218_ConPA_2026-10-28.zip   Exact predecessor and its dependencies.

Each table line is:
  state  read_symbol  write_symbol  direction  next_state
There are two lines per working state and no outgoing halt rows. Native
halt is 254; dense halt is 214 or 217. Native numbers are labels, not counts.
For example, native 218 is an ordinary working state.

REPRODUCE OFFLINE
----------------
Use Python 3.10 or later, standard library only. From this directory:

  python3 -B reproduce.py
  python3 -B reproduce.py --full
  python3 -B reproduce.py --full --report /chosen/path/replay.json

Default replay checks the release manifest, source and table reconstruction,
source control flow, proof-node bindings, both independent local proofs for
each reduction, saved runtime bindings/coverage, independently replayed blank
starts, and the predecessor audit. --full additionally rederives all 5,109
primary and 5,060 companion arbitrary-register symbolic cases. These cases
quantify over arbitrary natural registers and gaps and finite spare tails
through unary/list induction; they are not sampled small inputs. The bounds
on symbolic proof construction do not bound literal runtime.

No network, solver or proof-assistant installation is required. Temporary work
is removed; only an explicitly requested report is persistent. Runtime varies
with hardware. Saved receipts record the construction measurements. The final full replay
passed in 212.385 seconds here; its manifest count precedes adding the replay
receipt itself. The release manifest was then checked again. Editing
release files invalidates the manifest; retain an untouched copy for auditing.

REBUILD THE PDF
---------------
A normal pdfLaTeX installation is needed only to rebuild the document:

  cd paper
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF bytes may vary with TeX versions or timestamps. The main source includes
sections from ../proofs and the table appendix.

KEY IDENTITIES
--------------
Primary dense U214 SHA-256:
92e8243c1d17800ce5e7e3575f87244f4035d5ed96240a9ee911c410acfc631f
Primary native U214 SHA-256:
5fa7d923456ea7fb3e9cb331946e49750970bbffbfa755c0639bdaa9b7afd8a8
Reassigned source SHA-256:
9428a13d4c228e9760e8f546e43527ee5e196ae667ad2386ddabf961b477d083
Direct dense U217 SHA-256:
639da240bdb466f2a50ed40e36355a5677b6ecaaf5ef95e2e5309f4682b55be6

PROVENANCE
----------
Source repository commit: 1dd14d95976856bfabe06ab7294e78508556e0d1.
PROVENANCE.json pins the reviewed incoming archives. The primary U218 archive
preserves its U222 archive, original theory report, logical sources and
notices. New material follows the project's MIT No Attribution terms;
inherited third-party terms remain in licenses/.

Separate checks occurred within this assistant collaboration and are not
external human review. The report includes Further research questions and
distinguishes rejected leads from the accepted constructions.
