PA CONSISTENCY MACHINES: CROSS-ARCHIVE CONSTRUCTIONS AND REDUCTION SEARCH
13 November 2026

STATUS

The requested machine with fewer than 196 working states was not obtained.
This packet does not certify a 195-state consistency machine. The report
states this explicitly and distinguishes useful intermediate constructions
from the unsatisfied strict target.

START HERE

  report.pdf       Complete research report, including a full transition table.
  report.tex       Complete LaTeX source, with the accompanying .tex inputs.
  RESULTS.json     Machine-readable outcome and principal evidence.
  verify.py        Default portable replay; Python 3, standard library only.

NEW COMPLETE TABLES

  machines/diagonal_combined/machine.tm
    196 states; 3,676 source sites; 4,784 uniform instruction cases;
    exact blank startup 57,922 transitions.

  machines/separate_combined/machine.tm
    196 states; 3,649 source sites; 4,749 uniform instruction cases;
    exact blank startup 57,922 transitions.

  machines/diagonal_combined_zerojump/machine.tm
    196 states; 3,676 source sites; 4,785 uniform instruction cases;
    exact blank startup 58,168 transitions.

  machines/separate_combined_zerojump/machine.tm
    196 states; 3,649 source sites; 4,750 uniform instruction cases;
    exact blank startup 58,168 transitions.

Every dense table uses start state 0, working states 0..195, and halt 196.
Each line is: current-state read-bit write-bit L-or-R next-state.
The tape is binary, two-way infinite, and initially all zero. Moves are
one cell. The halt label is not included in the working-state count.

QUICK REPRODUCTION

  python3 verify.py

Run from this extracted directory with assertions enabled. This checks
SHA256SUMS before using the inputs, reconstructs all four tables, checks
every source case and exact complete startup tape, and runs the independent
source/CFG/graph/command and zero-jump reviews. It does not run the longer
heuristic or C++ search screens. A PASS validates the stated intermediate
claims; it does not mean that a sub-196 machine has been constructed.

The independent review imports neither the builder nor its symbolic tape
executor. It includes a general command compiler for nine versus ten
pushed entries, conditional Pop's early halt, and the dummy-zero convention
needed to preserve arbitrary stack tails. The zero-jump review recomputes
the common parent/child inductive source invariant.

OPTIONAL REPRODUCTION

  python3 research/verify_direct_negation_combined.py

This replays the separate 197-state, 3,444-site composition. In the directory
research/theory_study, python3 -B verify.py replays the 3,468-site composition,
and python3 -B replay_padded_failure.py reproduces the rejected padding
allocation. These commands do not repeat heuristic searches.

  latexmk -pdf report.tex

This rebuilds the report using an ordinary LaTeX installation. The directory
contains all .tex inputs. Recomputing the full original archive inventory
requires the original pinned incoming ZIPs in addition to this packet; their
digests and retrieval locations are recorded. Exact copies of the 127 prior
196-state tables are bundled, so the default replay also verifies the full
graph novelty comparison without those original ZIPs.

COMPARISON COVERAGE

  comparison/current_archive_comparison.csv
  comparison/current_inventory.json
  comparison/selected196.json
  comparison/verify_selected.py

All 27 top-level incoming ZIPs at the pinned revision were opened. Recursive
inventory finds 40 distinct ZIP payloads, 1,466 literal table members and 515
parsed-distinct tables. The 20 designated 196-state graphs are all different;
each has 196 ordinary action-bisimulation classes. Six rejected 195-state
constructions are identified. Diagnostic tables and nested duplicates are
not counted as accepted constructions.

The four new graphs also differ from all 127 parsed-distinct prior literal
196-state tables, including experimental and rejected tables. The independent
novelty checker examines every possible initial working label after its
necessary action-signature filter; the receipt records 23,324 rooted checks.

RESEARCH AND PROVENANCE

  research/                 Construction scripts, retained search inputs/results.
  independent_review/       Independent finite checks and command proof.
  inputs/axioms/            Exact supplied diagonal/separate components.
  inputs/combined/          Exact supplied Combined196 components.

The new scripts combine separately supplied improvements. The diagonal
calculus, Combined commands, zero-jump idea, and upstream engine remain
attributed to their respective prior reports. Original licenses are retained.
The local source repository was not changed. No remote write was performed.

ProveIt input commit:
  906367250a7f96c923147b10df392294bced7be5
James Chang PA196 snapshot:
  407cdc356f6b586635e71ac92be394255f4bfea4
James Chang PA209 snapshot:
  69d98241a721ead20b4f0b17df9062950b40fbfe

PROOF SCOPE

The supplied imported Lean endpoint establishes the internal implication
nonhalting -> Con(PA), not an exported closed biconditional. Several incoming
reports give ordinary mathematical calibration arguments for the converse.
This packet supplies exact new component bindings and the adjusted command
compiler, while retaining their uniform calculus-to-PA proof translations
as inherited mathematical components. No new end-to-end Lean or Rocq proof
is claimed. Finite startup traces are never used to infer nonhalting.

All negative searches have explicitly bounded templates. None proves a
general lower bound of 196 working states.
