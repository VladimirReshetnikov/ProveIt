Supplementary control-sharing and selector searches
==================================================

This directory preserves unsuccessful searches from the current investigation.
It contains no accepted machine below 194 working states. These finite search
results are not lower bounds on arbitrary Turing machines. The separately
delivered selector_obstruction certificate supplies an exact bound for one
explicitly restricted frozen-grammar template; its certificate is not duplicated
here.

All ordinary reproduction commands below are self-contained. They require
Python 3.10+ and, for the local-window searches, a C++17 compiler. Only the
optional MILP/LP discovery scripts require NumPy and SciPy with HiGHS. No Lean,
Rocq, network connection, or repository checkout is needed to replay the frozen
input searches. Use assertions: do not use Python -O or PYTHONOPTIMIZE.

Run commands from this directory; first create the output directory with

    mkdir -p rerun_outputs

Original observations are in recorded_logs/
and recorded_outputs/. Reproduction writes only rerun_outputs/, leaving the
historical logs intact. Wall-clock timings need not reproduce byte-for-byte.
No compiled executable or Python cache is included.

1. Quick integrity and rejected-candidate checks
-----------------------------------------------

    python3 -B check_package.py
    python3 -B sources/replay_known_candidate.py

The first command checks the manifest, reconstructs the PA194N6 native table
from its dense table and labels, verifies the sole append-zero mutation, checks
the 29,262 frozen contexts, and rebuilds the primary raw201 table. The second
replays the only quotient proposed by the more diverse whole-instruction
screen. It fails source contract (1164, None) after 1,518 completed contracts.
That failure is an executable-check failure, not a claimed literal countertrace.

2. Finite local-window reconvergence
-----------------------------------

    mkdir -p rerun_outputs
    c++ -O3 -std=c++17 sources/coalescence_merge.cpp -o rerun_outputs/coalescence_merge
    c++ -O3 -std=c++17 sources/coalescence_bypass.cpp -o rerun_outputs/coalescence_bypass
    rerun_outputs/coalescence_merge inputs/n6.native.tm 5 80 300 inputs/abstract_k5.txt > rerun_outputs/coalescence80.jsonl 2> rerun_outputs/coalescence80.log
    rerun_outputs/coalescence_bypass inputs/n6.native.tm 5 300 300 inputs/abstract_k5.txt > rerun_outputs/coalescence_bypass300.jsonl 2> rerun_outputs/coalescence_bypass300.log

Input: PA194N6, 194 working controls, native start 74 and terminal label 254.
The frozen context file contains 29,262 pairs (native control, 11-bit window).
Its bits are stored from the leftmost cell to the rightmost in increasing
binary place value; bit 5 is under the head. Both searches found zero candidates
and therefore have deliberately empty historical .jsonl outputs.

The common-action screen tries a shared replacement control for every tested
pair and every candidate action whose destination is an existing control, plus
one canonical halting action. It permits reconvergence after up to 80 original
steps and 300 replacement steps. The bypass screen deletes a non-start control
and independently rewrites its non-self incoming rows, with 300 steps on each
side. The replacement trace must not execute a modified row/control before its
meeting point. The reference trace is evaluated in the unchanged original table
and may visit those controls. At a nonhalting meeting point the complete finite
window, head offset, and control agree exactly; a halting original segment
permits arbitrary final tape/head effects. No trace may inspect outside the
supplied radius-five window. Self-entry behavior, the exact modified-row
avoidance filters, and the fixed numerical state labels are defined by the code;
these programs are specialized experiments, not general-purpose TM optimizers.

The contexts were inherited unchanged from the pinned QNS packet's additional
PA194N6 experiments. That packet derives them from source-site invariants,
symbolic primitive/list-block traces, unary-loop interiors, and startup. This
investigation freezes that input; it does not independently reprove the context
collector's coverage theorem. The upstream explanation is retained under
attribution/upstream_context_experiments_README.txt and is not a description of
new results in this directory.

An additional exploratory replay changed native row (198,0) from (1,L,40) to
(0,L,40), producing inputs/n6_append0.native.tm:

    rerun_outputs/coalescence_bypass inputs/n6_append0.native.tm 5 300 300 inputs/abstract_k5.txt > rerun_outputs/coalescence_append0_bypass.jsonl 2> rerun_outputs/coalescence_append0_bypass.log

It also produced no local candidate. The old frozen contexts have not been
proved complete for this altered machine, and the mutation has no supplied
blank-start/source invariant. This is a heuristic screen only, not a new
correctness or impossibility result.

Optional regeneration of the inherited contexts requires the pinned ProveIt
checkout, because the collector and all of its upstream invariant machinery are
not duplicated here. Set PA_CHECKOUT to the checkout at the commit below, then:

    PA_CONTEXTS="$PA_CHECKOUT/Computability/BusyBeaver/Research/PA/docs/pa194qns_research_2026-11-13/research/additional_reductions"
    python3 -B "$PA_CONTEXTS/abstract_r5/collect_contexts.py" inputs/n6.native.tm "$PA_CONTEXTS/inputs/sites.json" 58320 rerun_outputs/regenerated_contexts

The expected regenerated file patterns_k5.txt has SHA-256
73bd8c565c603c771a0862e529e1ad91bd98a606e8da7081708da55c01eb27fa.
Regeneration is optional and can take several minutes.

3. Symbolic whole-instruction reconvergence
------------------------------------------

    python3 -B sources/symbolic_merge.py > rerun_outputs/symbolic_merge.log
    python3 -B sources/symbolic_diverse_merge.py > rerun_outputs/symbolic_diverse_merge.log

Both programs reconstruct the primary PA194 table from its raw201 grammar and
seven folds. They consider only non-box controls and trial actions already
appearing in that table. The arithmetic/register box controls are protected and
handled by the inherited symbolic runtime; arbitrary register values enter
through its symbolic contracts, not numerical testing on small registers.

The first screen retains at most 24 distinct observed symbolic contexts per
state/read branch (7,684 retained contexts). The second retains the first visit
per state/read branch within each primitive contract, then selects at most 256
evenly spaced occurrences per branch (57,241 contexts). Preliminary replacement
checks have fuel 1,600. Surviving common actions are combined into simultaneous
two-control quotients and checked against all 4,780 source contracts with the
runtime's ordinary 1,024-step symbolic fuel. A failed check may mean failure to
prove the contract within this representation or fuel; it need not be a concrete
counterexample. The screening procedure is not complete for all semantically
valid mergers.

Both completed runs certified no quotient. The diverse screen tested one final
candidate: remove 2002 into 2031, with replacement rows (0,R,12) and (1,R,2003).
It failed the full contract check as recorded above. The first historical log
has per-control completion lines but no final DONE marker because that version
of the script did not print one; its process completed normally with no HIT.

4. Added selector helpers on the frozen raw201 grammar
----------------------------------------------------

    python3 -B sources/new_helper_search.py > rerun_outputs/new_helper_search.log
    python3 -B sources/two_helpers.py > rerun_outputs/two_helpers.log

A new helper has rows (0,R,u) and (1,R,v), with existing raw controls u,v.
Original action matches are tested before aliases. Folded reader pairs are
disjoint and have opposite, unique incoming bits. Helpers and destinations used
to implement a nontrivial branch avoid the pair being folded. The physical
simultaneous check, when reached, uses exact two-cell reconvergence with at most
20 replacement transitions. Optimistic matching is only an upper bound on the
number of compatible folds.

The one-helper screen enumerated 85 helper types able to supply all missing
branches of at least one raw pair. None supported even the optimistic nine-fold
matching needed for 201+1-9=193. The two-helper screen enumerated 1,039 useful
helper types and all 539,241 unordered distinct pairs. The largest optimistic
matching was nine, below the ten folds needed for 201+2-10=193. No simultaneous
candidate required validation in either target-count screen.

Optional solver-based discovery:

    python3 -B sources/arbitrary_helpers_milp.py > rerun_outputs/arbitrary_helpers_milp.log
    python3 -B sources/helper_lp_certificate.py > rerun_outputs/helper_lp_certificate.log

These two commands additionally require NumPy and SciPy. The MILP uses a
300-second limit and returned HiGHS optimum -7, giving the existing 194-state
construction in its relaxed model. The LP discovery script rationalizes the
dual and checks it exactly before writing a discovery record in rerun_outputs/.
That record predates the final certificate's provenance fields. The completed,
solver-independent verifier and final annotated dual are supplied separately in
the release's verification/helper_obstruction/ directory. Prefer that verifier
when checking the exact theorem. The exploratory solver output here is not
substituted for the exact certificate, and no duplicate certificate is stored.

5. Sequential and post-alias cascades
-----------------------------------

    python3 -B sources/cascade_helpers.py > rerun_outputs/cascade_helpers.log
    python3 -B sources/cascade_sequential_helpers.py > rerun_outputs/cascade_sequential_helpers.log

The first screen looked for a simultaneously compatible eight-fold quotient
after allocating one of the 85 single-fold-useful helpers. None existed in its
enumeration, so no cascade seed reached the following stage.

The sequential screen instead begins with every locally verified first fold
that actually uses the new helper. It then recomputes opportunities after each
alias and applies exact transition-bisimulation minimization and graph pruning
from start 74. This explores some equalities created by aliases, which are
outside the frozen-candidate LP theorem. It does not enumerate arbitrary new
helpers, arbitrary rewiring, every possible bisimulation representative, or
general multi-step TM transformations.

There were 97 initial seeds and 3,168 visited descendant tables, with best count
195. Each seed's search exhausted its queue in 16, 32, or 64 visits, below its
20,000-visit cap. Local fold validation uses the four previous-bit/current-bit
cases in a two-cell window and at most 40 transitions. The state counts and
queue closures are finite computational observations, not a global bound. There
is no accepted 193 table and therefore no new startup or arithmetic theorem.

6. Provenance and layout
------------------------

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 75a42a28ca818627f5a104fb0f0c7f7d02a52947

PROVENANCE.json records exact upstream paths and hashes. The primary compiler
and symbolic runtime in sources/base/ are unchanged copies from
PA/docs/pa194_conpa_2026-11-13/construction/. Minimal Program.lean,
Conjugacy.lean, and pa196.tm reference inputs come from PA/jamesyc-upstream/pa196.
The original repository-relative PA prefix is
Computability/BusyBeaver/Research/PA.

The new search drivers are the current investigation's experiments using those
inherited routines and conventions. Packaging changes are limited to relative
paths, isolated rerun outputs, explanatory module headers, and rejection of
disabled assertions; search algorithms are unchanged. The original licenses of
James Chang, ProveIt contributors, and Andrew James Wade are retained in attribution/.
Inherited evidence is credited to its source packets rather than described as a
new kernel-checked result.

sources/             Search programs and unchanged compiler/runtime dependencies
inputs/              Exact frozen machine, grammar, label, and context inputs
recorded_logs/       Original completed-run logs
recorded_outputs/    Original empty candidate lists and saved discovery data
recorded_summary.json  Structured finite-run scopes and receipts
attribution/         Source notices and upstream context explanation
SHA256SUMS           Integrity hashes for all shipped files except itself

No command in this directory establishes the requested PA consistency
biconditional for a machine with fewer than 194 states.
