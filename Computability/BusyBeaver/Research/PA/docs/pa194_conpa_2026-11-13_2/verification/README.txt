Independent audit of PA194
=========================

Run from the packet root:

    python3 -B verification/independent_verify.py

The --quick option omits only the two complete symbolic-runtime contract
lists. All literal-table, source, local-quotient, and exact-startup checks
remain active. No search, external solver, network access, or proof-assistant
installation is required.

What is independently reconstructed
----------------------------------
The verifier directly parses the dense 194 and native 194 tables. It requires
194 working controls,388 binary transition rows, a bijective relabeling,
start 0, separate halt 194, and graph reachability of every working control.
Its independently implemented compiler builds the 202-state unfolded table
from the grammar and pinned PA196 reference table. It then reconstructs all
eight disjoint identifications and compares the result with the delivered
native table. It does not import the candidate builder for these tasks.

The source parser expands the full program and resolves every successor by
subtree intervals and ancestor walking. All 3673 ordered primitive
instructions and their successors agree with the prior separate 190-token
source. The 190-token macro word also agrees. The full distributed source
listing is checked against this independent reconstruction.

Finite global quotient certificate
----------------------------------
All 23 incoming rows to the 16 folded roles write their prescribed history
bit and move right. Neither start nor halt is identified. This proves the
left-neighbor history invariant by one-step induction on the unfolded run.
For every folded role and both current symbols, the verifier simulates the
final, simultaneously folded table until the entire projected one-step
boundary is reached. All 32 cases use only cells -1 and 0; both cells match
the required endpoint exactly. Every other tape cell is unread and
unchanged. The durations are 1 in 12 cases,3 in 16 cases,5 in 3 cases, and 7
in 1 case. All unaffected rows commute with the quotient in one step.

Consequently every unfolded transition is simulated by a positive block of
at most 7 transitions. An unfolded halt after s steps gives a folded halt
after at most 7*s steps. If the folded machine halts after t steps, the
unfolded machine must halt within t steps: otherwise its first t+1 steps
would produce a deterministic folded run longer than its halting time.
This finite-sequence argument and the history induction formalize in PA.
The quotient theorem itself requires no consistency or soundness assumption.

Physical runtime and startup
----------------------------
All 46 rows in the 23 protected engine controls are unchanged from the pinned
baseline. This is stronger than the 45 row premises needed by the inherited
register-block theorem. For the full runtime pass, the audit uses the
unchanged hash-checked baseline symbolic executor; this executor is not a
second independently implemented kernel. Its 4780 contracts are generated
here from the independently resolved source graph. Both the unfolded and
folded tables pass every contract, for both decrement branches and the
symbolically represented arbitrary register files and header gaps.

A separate literal binary simulation of the blank tape reaches the complete
specified source seed frame after 58,154 transitions. The verifier checks
the entire finite set of one-cells, the head position -2, native control 84,
source ordinal 25, and the full register file; every other tape cell is zero.

Scope
-----
The executable certificate supports the compiler, source-graph, runtime,
and quotient parts of the mathematical proof. It is not a newly
kernel-checked Lean/Rocq proof of the end-to-end arithmetic consistency
biconditional. The logical calibration and its PA formalization are stated
and justified in the accompanying report.

Files
-----
independent_verify.py             Reproducible audit.
independent_receipt.json          Full-run receipt and exact hashes.
independent_local_certificate.json All 23 incoming rows and 32 complete traces.
independent_verify.log            Full-run output.
