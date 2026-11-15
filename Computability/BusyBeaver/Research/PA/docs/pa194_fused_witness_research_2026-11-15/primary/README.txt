PA194FW — fused negative-implication PA consistency machine
=========================================================

Result
------
This packet constructs a 194-working-state, two-symbol, one-tape Turing
machine. It changes the numerical axiom system and AX stack interface:

  h4 = E(H,D) -> (M(A,H) -> M(A,D))
  V  = U(D,N(E(H,D)))
  F45(D,A,H) = N(I(h4,V))

F45 replaces both h4 and h5=N(V). The exact fused negative implication is
classically equivalent to their conjunction. It is not literally the
inherited conjunction abbreviation, which would introduce an additional
double negation. The AX block now produces ten entries instead of eleven.
Its cached-generalization entry is U(A,h), with explicit command binder A.

The written proof gives an iPRA proof of blank nonhalting iff Con(PA), using
the identified prior written AX11H calibration for the same Foundation PA
refutation predicate. It proves the new logic equivalence, complete command
compiler, exact source binding and physical transport. The packet does not
claim a completed end-to-end Lean proof. No valid machine below 194 states
was found, and no optimality claim is made.

Machine convention
------------------
machines/PA194FW/machine.tm contains 388 lines, each:

  current_state read_symbol write_symbol direction next_state

Working states are 0..193, initial state 0, separate halt label 194. Both
symbols are 0 or 1, the initial tape is entirely zero, and the initial
head position is 0 on a two-way unbounded tape. A transition writes its
symbol, moves one cell L or R, and enters next_state; entering 194 halts.
The native labels use start 74 and halt 254. labels.json is the exact dense
conjugacy. Both rows are specified for every working state.

Dense table SHA256:
  8bc9eb53be619a30b37fbd40f47484045245b40fd04aa5f79763848c1ebc1224
Native table SHA256:
  716d31a1839b237a6a240a6c54adf895ed9ac7909e6ccb99e7e214c3f1729055

Reproduction
------------
Use Python 3.10 or newer, with assertions enabled and only the standard
library. From this directory run:

  python3 -B verify_all.py

This reconstructs the literal table from the frozen grammar and folds,
checks exact byte equality, replays every literal tape contract, verifies
the whole source/free-term emitter, regenerates the 419-line aggregate
fusion certificates, checks all nineteen symbolic command contracts and
audits all physical/source frame endpoints and clocks. It writes outputs
and logs under replay/. There is no network or Lean dependency. Full
literal replay may take several minutes. Do not run Python with -O or
PYTHONOPTIMIZE; these deliberately fail.

The construction-side symbolic runtime pass is redundant with the complete
independent replay and is omitted by verify_all.py. To reproduce it too:

  python3 -B construction/build.py --out rebuild/PA194FW

The independent verifier imports no construction code or arithmetic-box
oracle. Four generic list lemmas are reconstructed from literal rows.
SHA256SUMS.json records every frozen input and artifact; replay/ is excluded.

Recorded verification
---------------------
  Working states / rows:                    194 / 388
  Fixed + readers - fixed fold - readers:  135 + 69 - 1 - 9
  Primitive source sites / outcomes:       3695 / 4809
  Independent symbolic steps:              1130294
  Maximum per-contract symbolic steps:     403
  Reconstructed generic list lemmas:       4
  Whole blank startup steps:               57768
  Source macro tokens / arithmetic blocks: 191 / 949
  Symbolic abstract command contracts:     19
  Fusion join / left / right proof lines:  161 / 205 / 53

The literal contracts quantify over nine arbitrary natural registers,
both branches of every decrement, arbitrary affine nonnegative gaps,
and arbitrary nonempty finite spare lists, including the whole blank
exterior. Graph reachability of all states is checked. That does not
assert that every state occurs on the actual blank execution.

Mathematical dependencies and status
-----------------------------------
proof/fused_preservation.tex is the new proof. It is a TeX fragment using
amsmath, amssymb, amsthm and booktabs, with its own FW-prefixed notation.
The full report supplied with this packet integrates it and supplies PDF.

K, S and Peirce in the finite certificates are derived schemas from the
restricted rho axiom, not extra primitive axioms. Their independent
derivations are retained in references/logic/RestrictedImplication.lean.
The left projection also derives explosion from the retained ordinary h1.
This avoids using h4/h5 in the implicational basis or silently relying on
the removed independent-consequent witness to recover explosion.

The direct preservation path is:

  FW literal halt <-> FW scheduler halt <-> C_F refutation
                  <-> C_4 refutation <-> calibrated AX11H literal halt.

Its negation is combined intuitionistically with the prior written
AX11H Con(PA) equivalence. The previous absolute PA calibration uses its
documented model-uniform constructions and two negative-transfer endpoints;
this packet does not replace those by an unproved positive existential
PA-refutation equivalence in iPRA. The recorded finite programs establish
machine bindings, not a proof-assistant kernel check of all mathematics.

Ancestors and provenance
-----------------------
The repository snapshot compared is VladimirReshetnikov/ProveIt commit:
  883da8d55452ea097910ed2509a1eefc833ce292

The implementation ancestor is the incoming symmetric witness packet
pa194_symmetric_witness_research_2026-11-14, using its H5XS branch. Its
original notices and machine/runtime licenses are retained under references/
and construction/licenses/, and the independent verifier licenses under
verification/reference/. The construction vendor modules and independent
literal induction engine are attributed inherited code. The changes to
their callers, axiom emitter, grammar, folds, source binder and new proof
certificates are documented in PROVENANCE.json.

The calibrated logical ancestor is ordinary AX11H, not its H5X implementation
descendant. Ten updated written AX11H proof fragments are retained under
references/AX11H/. Their original source references remain visible; the full
repository calibration is not claimed to be formalized anew in this packet.

The comparison novelty certificate reports nonisomorphism to all 548
recognized spanning 194-state tables in the assembled current corpus,
including state relabeling, reflection, global tape-symbol exchange, all
possible roots and ignored actions on transitions into halt. This is a
finite-corpus comparison; it does not prove novelty against every possible
unexecuted generator or every published Turing machine.
