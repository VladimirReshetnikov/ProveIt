PA194AX11H: CONSTRUCTION, COMPARISON AND PROOF BOUNDARY
===================================================
Research prepared for Vladimir Reshetnikov, 14 November 2026.

Start with report/main.pdf. Its complete LaTeX sources are in report/.

RESULT AND LIMIT
----------------
This packet constructs a new binary, one-tape, blank-start Turing table
with 194 working states, named PA194AX11H. It composes the supplied AX11
eleven-entry/four-operand axiom operation with the supplied H cached-head
halt protocol. A corrected relative refutation compiler, independent
literal-tape certificates, exact startup, and a complete corpus comparison
are supplied. A separate countermodel proves that one proposed automatic-
freshness padding does not recover all old gate instances.

No valid machine with fewer than 194 working states was obtained.
The unconditional theorem

    iPRA proves Nonhalt(PA194AX11H) iff Con(PA)

IS NOT CLAIMED. The current repository leaves the machine-specific weak-
arithmetic calibration unfinished. This packet does not close that gap.
It supplies a new, verified relative construction, not a complete solution
of the stronger requested iPRA problem. The report distinguishes this
substantive missing argument from merely lacking a proof-assistant build.

MACHINE CONVENTIONS
-------------------
Authoritative file: machine/machine.tm
Alphabet: 0,1; two-way infinite tape, initially all zero.
Initial head: position 0. Initial state: 0.
Working states: 0 through 193. Terminal state: 194, not counted as working.
Each row: state, read symbol, write symbol, L/R move, next state.
Perform the write and move, then enter the destination. Entry into 194 halts.
There are exactly 388 rows. No terminal rows are supplied.

Dense SHA-256:
c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a

The native table uses start 74 and terminal 254. labels.json is the exact
dense-to-native bijection. The count is 134 fixed controls + 67 AX readers
- 7 simultaneous folds = 194. All 194 working controls are graph-reachable
from the declared start; no claim that all occur on the blank computation.

WHAT WAS CHECKED
----------------
* The machine rebuild is byte-identical to the frozen artifacts.
* Exact AX11-to-AX11H source splice: one removed increment, 3,671 retained
  instructions and all edges correctly relocated; five changed native rows.
* All 4,778 source outcomes pass both construction and independent replay.
* Independent literal checker: nine arbitrary natural registers, both
  decrement outcomes, arbitrary affine gap 48+n, arbitrary nonempty finite
  spare list, four generic list lemmas, no arithmetic-box oracles.
* Whole blank startup tape equals the source-25 frame after 57,922 steps.
* Thirty-one symbolic command identity/case checks include zero aliases,
  early halts, the four-field AX decoder, and the corrected final Pop.
* Exact graph comparison against all 83 current 194-state frontier objects:
  no match under arbitrary state renaming, all spanning roots, reflection,
  bit exchange, and irrelevant terminal write/move effects.
* All 535 existing official catalogue representatives were recounted and
  matched by the separate census. Historical proof suites were not all rerun.

These are executable mathematical certificates, not Lean/Rocq kernel proofs.
Finite startup is not used as evidence of infinite nonhalting.

REPRODUCE OFFLINE
----------------
Requirements: Python 3.10+ standard library; recorded run used Python 3.12.
Keep assertions enabled: do not use -O or PYTHONOPTIMIZE.

    python3 verify_all.py --output /tmp/ax11h-verification

This rebuilds in a temporary directory and checks all primary certificates.
It verifies SHA256SUMS when the manifest is present. It does not rerun the
optional long bounded searches. Saved replay results are under
verification/replay/; the final integrity manifest was generated afterward.

For construction alone:

    python3 build.py --output /tmp/ax11h-machine

The --quick option skips the construction-side symbolic replay and is not
full verification. Neither command overwrites the frozen machine directory
unless the caller explicitly chooses that output path.

For the PDF, enter report/ and run pdflatex twice on main.tex. A normal
TeX Live installation with the standard packages listed in main.tex is
sufficient. The compiled PDF is already included.

ARCHIVE MAP
-----------
report/         Complete paper, LaTeX inputs, full 194-state table appendix,
                all 72-delivery and 83-frontier comparison appendices.
machine/        New literal tables and all construction/certificate data.
inputs/         Exact pinned predecessor data for an offline rebuild.
construction/   Attributed inherited compiler and support.
verification/   Independent tape checker, reference modules and final replay.
proof/          Command/emitter/graph checks; countermodel proof and code;
                weak-arithmetic audit and independent mathematical review.
comparison/     All recognized stored tables and their provenance; complete
                delivery ledger, frontier annotations and census algorithm.
research/       Explicitly unsuccessful 193-state repair and grammar searches.
references/     Inherited ordinary PA arguments and pinned status documents.
licenses/       Retained upstream licenses.
PROVENANCE.json Exact commit, sources, copied-file hashes and scope.
SHA256SUMS      Integrity hashes of every deliverable file except itself.

CORPUS SCOPE
------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 1c9524d8bf2e0a27b9a16ff622359927f536e663
Directories: Computability/BusyBeaver/Research/PA and docs/incoming.

72 deliveries = 61 filed research packets + 11 incoming ZIPs.
83 distinct stored 194-state fingerprints = 82 spanning graphs + one
disconnected diagnostic. Historical categories: 40 principal, 7 supplementary,
25 auxiliary, 4 seeds, 6 rejected, 1 diagnostic. These are reported historical
statuses, not 83 newly proved consistency machines.
53 stored 193-state tables are research/rejected objects; none is accepted
here as a blank-start PA-consistency machine.

The recognizer covers explicit tables and specified JSON encodings, including
nested ZIPs. It does not execute arbitrary generators or infer literal tables
from prose. See comparison/README.txt for exact recognition and equivalence
conventions. Optional ZFC, DiophantineConsistency and ConciseIPRA sources were
inspected for relevant ideas, not rebuilt as part of this packet.

ATTRIBUTION
-----------
The AX11 and H mechanisms, numerical calculus, compiler, existing tables,
and inherited proof infrastructure are credited to the ProveIt research
packets and their antecedents, including James Chang and Andrew James Wade.
This packet's new contribution is the composition, its relative verification,
the current comparison, the specified padding obstruction and additional
bounded searches. No global priority claim is made. See NOTICE.txt,
PROVENANCE.json and licenses/.
