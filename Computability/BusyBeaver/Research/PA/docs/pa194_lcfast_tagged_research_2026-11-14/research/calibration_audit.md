# Focused independent review of the revised AX11H written calibration

## Exact dependency

The reviewed bytes are the nested `reference/ax11h_written_calibration.zip`
inside `docs/incoming/pa194_research_2026-11-14.zip` at ProveIt revision
`8d31445d858761a8f6150c2e5012adae8895e932`.
The nested archive SHA-256 was recomputed as
`93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`.
The same bytes are imported by the loop-continuation packet as
`reference/ax11h_calibration_603c58c.zip`.

The final theorem appears in `proof/consistency_equivalence.tex`. Its literal
parent tables are `machines/PA194AX11H/machine.tm` and
`machines/PA194QAX11H/machine.tm`. The primary AX11H dense-table SHA-256
reported by the importers is
`c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a`.
The theorem's consistency sentence is `nativePAConsistency`, negating the
mapped current Foundation PA refutation predicate; the Foundation pin is
`32e1a0956a8622fad067328ca1959729a7634428`.

## Assessment

This is a substantial written calibration, not just an assertion that an
ordinary standard-model simulation automatically internalizes into iPRA.
No blocking mathematical defect was identified in the particular high-risk
arguments reviewed below. This statement is narrower than independent
verification of every cited source recipe. There was no new end-to-end Lean
or Rocq build, no implementation of the entire PA proof compiler, and no
independent rechecking here of each of the roughly 700 retained reference
files. The dependency should be presented as a precisely pinned imported
written theorem. A new machine's independent relative transfer should be
stated separately, so the status of the absolute theorem is transparent.

## High-risk interfaces reviewed

1. **Finite-demand recursion and weak induction.** A query's finite child
   queries are computed before their proof values. Same-stratum calls
   strictly decrease a numerical source rank. A full binary tree of depth
   r+1 has at most 2^(r+2)-1 slots, so query generation and reverse proof
   evaluation are primitive recursive even when environments and proof
   codes grow dramatically. No boundedness by the original input code is
   required. The forward and reverse correctness predicates are bounded
   conjunctions of primitive-recursive tests, represented by Boolean
   characteristic functions; thus the proposed induction is quantifier
   free. This is a sound general way to replace a naive induction over
   all environments.

2. **Term-supplier stratification.** The term completion explicitly handles
   the danger that a substituted variable can denote a term larger than
   the original variable code. Totality, coherence and uniqueness are
   completed first. Higher vector-realization leaves call these completed
   lower-stratum functions rather than claiming a same-rank recursive
   decrease. The displayed call architecture therefore avoids the obvious
   recursive-cycle objection.

3. **Current Foundation endpoint.** The adapter distinguishes Foundation's
   square pairing and falsity code 13 from the numerical calculus's Cantor
   pairing and contradiction code 1. Its induction-axiom witness search
   bounds the matrix K by the computed opened-body code, not by the outer
   axiom code. The opening/closing proof constructors are specified as
   finite sequent-rule constructions. The changed `addEqOfLt` axiom is
   explicitly weakened by an existential-projection proof; the historical
   and current arithmetic bases are compared as well.

4. **Arithmetic templates.** The source-command completion specifies the
   primitive increment/decrement/jump templates, with exact clocks for
   pairing, unpairing, copying and comparison. The clocks are sums and
   primitive recursions on input values, not unbounded exit searches. The
   four-field AX parser includes its actual extra MP operand. Scratch
   preconditions and the fallthrough effect are explicit.

5. **All-store command completeness.** The candidate scheduler carries its
   store between candidates; the proof does not assume resets. The
   compiler uses a uniform prefix to normalize any incoming store, then
   an all-store halting suffix. The bound Phi_K(s), defined as a finite
   maximum over command/store codes, is primitive recursive and monotone.
   Its iterates at L(N-1-j) give the required decreasing input budgets for
   earlier proof-line calls. The residual after a command is at most the
   selected seed; for a positive continuation it is at most ell-1.
   Consequently each candidate drains within its seed plus one commands,
   and the final square bound on reaching/draining the selected candidate
   is conservative.

6. **Physical simulation and reverse witness.** Complete tape halves are
   encoded by binary integers, with an absorbing halt code. The symbolic
   checker rules are reduced to literal transitions, unary-run induction,
   four list traversals, and finite-word identities. The gap and spare list
   are explicit state components. Positive local durations give the reverse
   witness t+1: if a physical run halts at t but source step t+1 is live,
   synchronization produces a nonhalting physical configuration after t,
   contradicting absorption. This uses decidability of the finite halt-code
   equality, not Markov's principle or an unbounded least-hit search.

7. **Reverse logical soundness and final transfer.** The reverse argument
   uses Sigma_1 induction in I-Sigma_1 models on a vector of PA proof
   witnesses, rather than falsely calling PA provability quantifier free.
   The claimed iPRA negative equivalence then goes through the separately
   cited conservation/negative-translation endpoints. Both directions use
   the same mapped PA refutation predicate and literal halting function.

## Further verification that would materially strengthen confidence

Implement the complete direct derivation-list compiler and check its local
recipe outputs against the direct C4 checker; then formalize the generic
finite-demand theorem once and instantiate it for the listed strata. This
would make the large cited recipe dependency executable without conflating
that step with a formal proof of every arithmetic invariant.
