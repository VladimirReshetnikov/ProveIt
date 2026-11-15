Physical-engine research and reproducible rejected candidates
=============================================================

Accepted secondary machine: PA194OR
-----------------------------------

machines/PA194OR contains the new operand reassociation with the primary PA194
source as its parent. It has 194 working states, 388 binary rows, 3,673 source
sites and 4,780 source outcomes. Six literal rows differ from its parent. The
closed operand macro changes from ((A,(B,C)),D) to (A,(B,(C,D))), where
A=node32, B=node53, C=node55 and D=node65. The 67-leaf routine occurs twice,
so 134 source addresses change. Its resolved source instruction graph is exactly
unchanged. The arithmetic register engine is unchanged.

The apparent one-state saving in that reassociation required restoring a hidden
backward history selector. From q69 scanning a current 0, the previous tape bit
is h. For h=0 the old path is 69 -> 213 -> 92 -> 104; the new path is
69 -> 92 -> 111 -> 104. For h=1 the old path is 69 -> 213 -> 90 -> 105;
the new path is 69 -> 92 -> 90 -> 105. Each path takes three steps and ends
with the same head, state and unchanged tape. The complete two-cell traces are
machines/PA194OR/structural_audit.json. This extra selector consumes the state
that the operand reassociation otherwise appeared to save.

The independent literal checker proves all 4,780 source contracts using nine
arbitrary natural registers, arbitrary natural gap, and an arbitrary nonempty
finite spare list. It derives four list lemmas from the literal table and uses
no arithmetic box oracle. Exact blank startup takes 58,170 steps. The receipt
and all affine contracts are in machines/PA194OR/independent/. Its dense hash is
379e12957eafc5ecb1ec04868067fe931af913e7bc46e69a36b6067d83c4c79f.

Reproduce with the standard library only, from the archive root:

    python3 -B construction/build_or.py --output /tmp/PA194OR
    python3 -B verification/check.py /tmp/PA194OR

The new local and runtime proofs give a relative equivalence to the primary
parent. The main PA194ORH construction in this archive instead uses the AX11H
parent for which the supplied archive has the preferred written iPRA calibration.
Neither construction is claimed here to have a completed Lean proof.

relative_OR.tex supplies the secondary relative iPRA argument, with explicit
absorbing-halting witness transfer clocks:

    H_primary(t) -> H_OR(58170 + 13*(t+1)^2 + 681*(t+1))
    H_OR(t)      -> H_primary(58154 + 13*(t+1)^2 + 681*(t+1)).

The inherited parent literal contracts and hash-bound receipts are included in
relative_OR_parent/. The ordinary written proof is separate from these finite
bindings; the latter can be replayed with:

    python3 -B research/engine/relative_OR_check.py

This checks exact source identity, all 4,780 outcome indices and coefficients
for both tables, address/head closure, the two selector identities, and the
coefficient envelope used in the displayed clocks. Its output is
relative_OR_inspection.json. The parent's Con(PA) calibration remains explicitly
inherited; the new relative proof does not silently establish that calibration.

Rejected 193-state operand candidate
-----------------------------------

rejected_operand193/ preserves the literal candidate, source tree, instruction
graph, seven folds and original failed receipt. The source graph and all local
fold identities pass, but the universal runtime check fails first at source
site 11, zero branch (physical register 0). The state q213 was also used backward
by q69 and could not be changed solely on the basis of its source decoder role.
There are 30 failed source outcomes, listed in repair_candidate_symbolic.json.
Changing q69/0 to each of the 772 possible write/move/remaining-working-target
actions did not repair them. That screen did not include direct halting targets;
it is recorded as a restricted repair screen, not a lower-bound result.

Rejected 193-state scanner candidates
------------------------------------

The shortened return scanner deletes native q34 by changing q23/0 to 0L75.
The attempted coupling also reassociates the root and node164, swaps the two
history-selector branches, and requires the AX occurrence of node72 to arrive
with preceding history bit 1. A breadth-first association search around that
occurrence explored through depth 6 with a 10,000-tree frontier cap, generating
61,847 distinct seen trees. Forty state-count nominees (five 193, thirty-five
194) passed source-graph equality and the simultaneous local fold identities.
All forty failed source validation, first at site 50 or 76. Full result records
are in rejected_scanner193/summary.json.

The retained first 193-state table fails at site 50. Its source path is
101101001000000000 and contains a run of nine zeros, which the shorter scanner
cannot distinguish from header padding. The rejected tape-symbolic trace is
included. A follow-up search through depth 7 with the same frontier cap generated
100,634 seen trees and found no tree meeting both history-bit 1 and an internal
zero-run bound of five. No claim about unrestricted grammar optimization follows.

Replay both retained failures with:

    python3 -B research/engine/check_rejected.py

Replay the two bounded association searches with:

    python3 -B research/engine/search_scanner.py --output /tmp/scanner-search
    python3 -B research/engine/search_scanner_bounded.py --output /tmp/scanner-bounded

The first search processes seven levels (depths 0 through 6); the second processes
eight. Both accept --depth to limit the number of levels. engine_helpers.py is
the unmodified utility prefix of the pinned loop-continuation packet's
construction/build.py, and engine_foldscreen.py is its unchanged
research/search_support.py. Their original source path is
Computability/BusyBeaver/Research/PA/docs/
pa194_loop_continuation_research_2026-11-14/. The search wrappers are new.

Physical quotient and common-future screens on accepted PA194OR
-------------------------------------------------------------

The two supplied C++ search engines were rerun on the new PA194OR table at
radius 6, using an inductively closed overapproximation with 268,539 local
contexts. It starts from the blank initial window and admits both values for
each newly exposed boundary bit. The recursive two-state quotient scan examined all 18,721 unordered
working-state pairs and 1,210,905 candidate joint row definitions, with at most
64 replacement steps. It found no successful quotient. The common-future
two-state quotient scan used at most 16 old steps and 128 replacement steps and likewise
found no successful quotient. Empty *.jsonl hit files and the full logs are
included. These are explicitly bounded local transformation searches.

Reproduce from the archive root (a C++17 compiler is required):

    g++ -O3 -std=c++17 research/engine/node75_recursive_folds.cpp -o /tmp/recursive
    /tmp/recursive machines/PA194OR/machine.native.tm 6 64
    g++ -O3 -std=c++17 research/engine/node75_multisync.cpp -o /tmp/multisync
    /tmp/multisync machines/PA194OR/machine.native.tm 6 128

These C++ files were copied from pa194_sf_research/research/physical/code/ in the
supplied incoming pa194_comparison_and_new_designs_2026-11-15.zip at repository
commit 43d9041f5571936c45c583f7f9d7f6eed9e0fd84. The original licenses included
in this archive apply. The search method is inherited; applying it to PA194OR
and the operand/scanner constructions and diagnosis are new.

Scope and omissions
-------------------

Other exploratory fragment searches and SMT runs were abandoned or incomplete.
They are not included as exhaustive negative results. In particular, no result
here establishes that a 193-state machine with the required logical property
is impossible. The accepted deliverables remain PA194ORH and PA194OR, both with 194 states.
