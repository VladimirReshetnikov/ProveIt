PA194QNS: A NEW 194-STATE PA-CONSISTENCY MACHINE
================================================

Result
------

No verified construction below 194 states was found. The requested same-size
alternative is PA194QNS, a new composition of the existing Q axiom emitter,
no-push modus ponens and symmetric implementation of the original sum-based
Shift guard. Its exact graph is different from all 39 previously delivered
194-state graphs at the pinned repository snapshot, even allowing arbitrary
state renaming, a change of spanning root, left/right reflection and global
symbol exchange. The component mechanisms are attributed, not claimed as new.

The ordinary mathematical proof gives

  PA proves: not Halt(PA194QNS, blank) if and only if Con(PA).

The new finite-trace equivalence is composed with the explicitly identified
inherited PA calibration. This is not a newly compiled end-to-end Lean/Rocq
proof, and no completed internal iPRA consistency theorem is claimed. The
executable certificates do not infer infinite nonhalting from a finite run.

Read first
----------

  report/pa194_qns_research.pdf    Main report, full comparison and literal table
  report/pa194_qns_research.tex    Main LaTeX source
  report/calculus_proofs.pdf      Complete logical transports and command proof
  report/calculus_proofs.tex      Supplementary LaTeX source
  RESULTS.json                   Machine-readable aggregate findings

Principal machine
-----------------

  construction/machine/machine.tm

Each line is: state, read bit, write bit, direction, next state.
Working states: 0 through 193. Initial state: 0. Halt label: 194.
One two-way infinite binary tape, all zeros initially, head at coordinate 0.
Every action writes a bit and moves exactly one square L or R.
There are 194 working states and 388 rows; the halt label is not counted.

Dense SHA-256:
  7eb36aea69e5de46cc47fa7aab0191f191657ab500dafb808dc3c394640591b8

The native-label table, source tree, resolved instructions, physical register
map, local fold cases and construction receipts are adjacent. The budget is
135 fixed controls + 67 AX readers - 8 simultaneous folds = 194.

QN has 3,654 primitive instructions and QNS has 3,651. Instructions 0..3648,
including all their successors, are identical. The sole entry to the changed
tail ensures H=0. The old five-instruction tail presents comparator operands
(x,1); the new two-instruction tail presents (1,x). The common destructive
comparator halts exactly on equality and otherwise clears both operands.
Thus the changed blocks have identical halting and exit-store behavior.

Fresh verification
------------------

Both physical symbolic engines checked all 4,751 source outcomes. The first
uses inherited arithmetic-block contracts; the independent literal checker
rederives four list-sweep lemmas from the actual table, imports no source
compiler and checks every primitive case on complete symbolic tapes. The
checks quantify over arbitrary natural registers and the stated spare-list
and affine-gap interfaces. They are not bounded samples of register values.

The first engine performed 1,512,246 symbolic steps; the independent engine
performed 1,106,186. Exact blank initialization takes 58,004 physical steps
and is compared on the whole tape. The source-tail equivalence, all 32 fold
cases, exact dense/native conjugacy and graph novelty were checked separately.
Receipts and complete per-contract evidence are in construction/evidence/.

Reproduction
------------

Python 3.10 or later and its standard library suffice for the main checks.
Keep assertions enabled (do not pass -O or set PYTHONOPTIMIZE).

  python3 -B verify_all.py

This verifies the archive manifest, reconstructs the principal table in a
temporary directory, replays both physical engines, checks the independent
source equivalence and graph novelty, and verifies the finite exchange DAG.
It does not rerun heuristic searches or overwrite the published machine.

  python3 -B verify_all.py --quick

The quick version still checks integrity, exact reconstructed bytes, local
folds, whole blank startup, source equivalence, novelty and the exchange DAG;
it explicitly omits the two long universal physical replays. Both full engines
were executed for the delivered machine before packaging. The final relocated
quick replay is an additional packaging check, not an extra full replay.

  python3 build_report.py

This compiles both PDFs with pdflatex until cross-references stabilize. A usual TeX Live installation
with AMS, Latin Modern, microtype, geometry, booktabs, longtable, tabularx,
enumitem, xcolor, xurl, hyperref, fancyhdr and needspace is sufficient.
Build intermediates go to a temporary directory. Rebuilding PDFs may change
their byte hashes because of TeX timestamps or environment differences;
the original manifest describes the distributed files.

Comparison and source provenance
--------------------------------

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 317b07268681b44ff352d173a162e2a8c241b2fe
Report date: 13 November 2026, Pacific time.

comparison/packet_ledger.csv and .json list all 54 current deliveries.
comparison/frontier194.csv and .json list all 39 existing 194-state classes.
comparison/current_census/ contains the full census and all 721 distinct
table byte presentations, including larger machines and research fixtures.
The classification distinguishes 26 reported 194-state constructions, nine
auxiliary/search graphs and four rejected graphs. It does not treat each
reported construction as a completed proof-assistant calibration.

The census recognizes complete numeric five-column binary tables with one
separate halt label; narrative review complements that literal-table scope.
The full census has 497 action-graph classes admitting a spanning root.
There is no such complete graph with 7..193 working states in the census;
small disconnected 6- and 9-control synthetic fixtures are not candidates.
No census or failed search is asserted to prove global minimality.

construction/PROVENANCE.json identifies exact inherited inputs and hashes.
construction/references/ retains the ordinary mathematical dependencies.
Inherited code and documents retain their attribution and license files.

Secondary construction and research
------------------------------------

research/tag196n/ supplies TAG196N, a verified 196-state machine with a new
formula encoding: universal and equality constructor residues are exchanged,
while implication, membership, truth 0 and contradiction 1 are preserved.
Its mathematical transport recodes variable labels as well as formulas and
explicitly repairs the nonmonotone numerical side condition using rho8All.
Its complete N-controller command compiler is supplied. The state count is
135 + 71 - 10 = 196. This secondary result does not improve the 194 bound.
It has a full first-engine symbolic check and independent emitter, splice
and source-binding audits; the full second physical checker run for QNS is
not claimed for TAG196N. Its own README gives replay commands.

proofs/ contains the 61-node K/S/MP exchange certificate, generator and
independent certificate replay, complete mathematical proof fragments and
the relevant inherited Lean source.

search/ records the exact 64-case composition screen, local contractions,
139,968 parameter assignments and bounded grammar searches. Its README and
FINAL_RESULTS.json give commands, seeds, counts and explicit limitations.
The new QNS-specific radius-six contraction record is qns_local6.json;
replay it from this directory with:

  node search/local_search.cjs construction/machine/machine.native.tm 74 6 256

That optional search found no contraction in its sufficient local model.
The largest completed exchanged-head search reached a projected 197 states;
the alternate-tag search remained at 196. Search scores alone are not proof
certificates. The accepted QNS and TAG196N tables have their separate checks.

Integrity
---------

MANIFEST.json records the relative path, byte length and SHA-256 of each
distributed file except itself and the top-level SHA256SUMS. SHA256SUMS also
binds MANIFEST.json. Subpacket checksum files describe their own recorded
contents. The top-level verifier uses the complete top-level manifest.

NOTICE.txt summarizes attribution and proof boundaries. The main report ends
with specific further research questions about joint grammar/fold allocation,
larger local equivalences, register interfaces, formula tags and formalization.
