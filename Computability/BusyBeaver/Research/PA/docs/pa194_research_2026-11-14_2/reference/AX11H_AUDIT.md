# Audit of the new incoming AX11H written calibration

Repository snapshot: `VladimirReshetnikov/ProveIt@1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.

Audited incoming archive: `docs/incoming/pa194_ax11h_research_2026-11-14.zip`.
Its own source pin is `1c9524d8bf2e0a27b9a16ff622359927f536e663`; its current
Foundation dependency is `32e1a0956a8622fad067328ca1959729a7634428`.

## Result of this review

The latest incoming archive contains a substantive **written, unconditional
iPRA calibration claim**, unlike the older filed AX11H packet. Its two literal
tables are byte-identical to the already filed AX11H and AX11QH tables. The new
contribution of this incoming archive is the expanded mathematical completion,
not two previously absent transition graphs.

I read the physical/source, source/command, abstract command compiler,
Foundation adapter, term-supplier, forward-calibration, reverse-soundness and
final-composition arguments. I checked representative crucial constructor
recipes against the retained Lean source, and replayed the aggregate finite
checks. **No blocking mathematical defect was found in the inspected chain.**
This is not an independent kernel verification of the approximately 700 retained
Lean reference files or of the complete new proof compiler. The complete forward
compiler is specified mathematically; the archive does not implement or run that
whole compiler. That is an implementation/verification limitation, rather than
by itself a missing premise in a written mathematical proof.

The repository's main README still describes its machine-specific Lean/iPRA
endpoint as open. That statement must be reconciled with this later incoming
written theorem; it is inaccurate to summarize every current incoming report as
claiming only relative or conditional preservation.

## Exact machines

| Incoming name | Dense-table SHA-256 | Already filed counterpart |
|---|---|---|
| PA194AX11H | `c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a` | `PA/docs/pa194_ax11h_research_2026-11-14/machine/machine.tm` |
| PA194QAX11H | `19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50` | `PA/docs/pa194_ax11qh_research_2026-11-14/candidate/machine/machine.tm` |

Here `PA` abbreviates `Computability/BusyBeaver/Research/PA`.
Both have 194 working states, 388 rows, blank start state 0, and terminal 194.

## Physical/source bridge

The paper `proof/physical_ipra_audit.tex` supplies considerably more than finite
test evidence. It represents the complete tape by two binary integers, with a
single canonical arithmetic halt code; states and head movement are explicitly
related to the symbolic interpreter. It interprets affine tape-run lengths and
ties the list-width variable to the same arbitrary finite spare list represented
by each symbolic list atom.

Every symbolic rule receives an arithmetic proof: literal rows by substitution,
unary self-loop sweeps by length induction, normalization by finite-word
identities, and four whole-list sweeps by prefix-length induction. These
arguments use quantifier-free invariants in primitive recursive functions.
The symbolically finite certificate replay supplies the concrete instances; it
is not promoted to a uniform theorem without those rule proofs.

The proof explicitly checks the 4,777 nonhalting padded source endpoints, handles
both decrement branches, preserves all nine registers and both tape exteriors,
and carries the increasing gap and nonempty spare list through the source-frame
recursion. The exact duration for each live source step is affine, with positive
constant at least 3. The finite startup is exactly 57,922 literal steps.

For source run `z_k`, it defines a primitive recursive cumulative clock `tau(k)`
and proves `Run(57922 + tau(k), blank) = E(z_k)`. Duration is zero after the
canonical source halt. The reverse implication correctly uses the guarded bound
`z_k != Halt -> tau(k) >= 3k` and reverse witness `k=t+1`; it does not incorrectly
claim the clock remains cofinal after a source halt. Absorbing physical halt and
decidable source halting complete that argument intuitionistically.

## Source/command bridge

`proof/source_command_completion.tex` gives explicit primitive templates for
Cantor unpairing, pairing, clear/transfer/duplicate, multiplication by four, and
destructive comparison. It supplies their exact iteration clocks. The checker
matches all 3,671 source instructions and their outgoing edges to these
independently generated templates, and a free-expression calculation checks all
190 AX tokens and the complete guarded output tuple.

The proof addresses the dangerous interface changes explicitly:

- AX really consumes four fields; the final field `z` is read by full MP
  fallthrough and survives as the offset even when nonzero.
- The saved generalized theorem is `U(d,h)` for these two tables.
- Shift tests cached `h=1`; visible `t=1` alone is insufficient.
- A halting Shift retains the exact halted source register file.
- The fresh candidate counter increments at candidate selection, matching the
  literal fetch code, while the carried store is retained between candidates.

It constructs a positive primitive recursive command/source clock `theta`,
including an absorbing Done-state representation, and applies the exact
simulation induction. This removes the formerly separate source/command
interface for these two literal sources.

## Abstract compiler and scheduling

`proof/ax11h_preservation.tex` uses the correct H refutation suffix `Pop`, not a
plain final Shift. It supplies all-store Push/Pop/Discard/selector identities and
reserves a dummy zero in the no-push MP compiler so that the arbitrary underlying
stack is preserved. Total Cantor projection equations handle zero aliases.

The all-store compiler induction is not silently induction on an unbounded
universal-store statement. For a proof list of length N it bounds all compiled
words by L and their command codes by K, builds a primitive recursive monotone
store bound Phi, and proves correctness for finite sets of stores bounded by
`B(j)=Phi^(L*(N-1-j))(s0)`. Its bound satisfies
`i<j -> Phi^L(B(j)) <= B(i)`, which covers the actual inputs to earlier premise
words. The induction assertion is a bounded Boolean conjunction.

The command word encoding uses the correct AX field order `y,x,z`, candidate
continuations decrease, and an explicit extra AX prefix makes a universally
halting proof word occur cofinally in the unchanged store-carrying enumeration.
No assumption that failed candidates reset the store is used.

## Forward logical compiler

The main new technique in `proof/term_leaf_completion.tex` and
`proof/forward_calibration_completion.tex` is sound as an arithmetic method.
For each recursive family the query to every child is computed from the input
before any returned proof is used, and its source rank decreases. The complete
binary query tree has a primitive recursive size bound (at most `2^(r+2)-1`).
A forward bounded loop generates requests, and reverse evaluation builds proof
lists. Two Boolean invariants establish query validity/coverage and checked
outputs. Parameter growth is allowed because it occurs inside an explicitly
bounded primitive recursion. There is no unjustified extraction of a primitive
recursive choice function from arbitrary `forall x exists y` statements.

The paper supplies the critical lower interfaces separately: direct restricted
rho/MP/Gen proof-list constructors, the diagonal replacement for obsolete
primitive equality vacuity, source translation and label relocation, fixed
relational templates, closed finite relational proof seeds, and
arbitrary-property separation. It treats stored numerical proof values as direct
lists, rather than assuming the upstream full-PA `verifyValue` theorem has
already been weakened.

Term totality and coherence recurse on source terms; uniqueness is a completed
lower stratum; vector realization can therefore call uniqueness on a substituted
term whose code is larger than the original bound variable. The paper correctly
identifies and resolves this rank hazard. The binder/canonical guard suppliers,
arbitrary induction matrices, and universal closure are explicitly included.
The outer proof compiler recurses on strictly smaller actual proof children and
uses the precise requested-label maps.

Representative retained source recipes inspected against the paper include
`NumericPAeqValueCertificateComposition.lean`,
`FoundationRelationalSequentAllocator.lean`,
`RelationalPredicateTemplateLKBounded.lean`,
`RelationalPredicateTemplateNDPadded.lean`,
`RelationalClosedCertificateSeeds.lean`, and
`PAInterpretedFixedCertificateSeeds.lean`. Their displayed local constructors
and padding/recursion dependencies agree with the replacement recipes used in
the written argument. This review did not replay every supplied Lean import.

## Foundation predicate and reverse direction

The Foundation adapter distinguishes current Foundation PA, historical PA, and
ordinary PAeq. It explicitly handles square-pairing syntax (falsity code 13)
separately from the numerical Cantor calculus (falsity code 1). It gives
OpenOne/CloseOne proof constructors and uses bounded witness extraction for
canonical induction matrices, including the bound on the opened matrix rather
than incorrectly bounding it by the closed axiom code.

The current and historical finite bases differ in `addEqOfLt`; the paper supplies
the logical projection to the current weaker axiom and a finite derivation of
the historical bound from the current order axioms. It also accounts for the
historical prenex Sigma1 hierarchy inside the current hierarchy before reusing
historical I-Sigma1 model lemmas.

For numerical-refutation to PA-refutation, the proof cites the already supplied
model-uniform seed/rule soundness and completed guarded gate. It uses Sigma1
induction on a finite vector of PA proof witnesses; it does not call an
unbounded provability invariant quantifier free. The current one-way transfer
theorems then yield both negative iPRA implications without Markov's principle.

## Verification records and limits

Fresh quick replay: `ax11h_fresh_quick/summary.json`, **PASS**. It checked 1,186
manifest members, both literal table reconstructions, stored endpoint/duration
certificate bindings, source-command bindings, finite Foundation proof
constructors, 119 current/historical coding equations, and the fixed
premise-exchange certificate. Quick mode did not replay the construction's
symbolic instruction contracts or the independent literal instruction suite.

Fresh full replay: `ax11h_fresh_full/summary.json`, **PASS**, completed for
both AX11H and QAX11H. It repeated those checks and additionally rebuilt both
construction symbolic-contract certificates and both independent literal
source-contract suites. Each machine passed all 4,778 source outcomes across
3,671 source sites, all four generic list-sweep lemmas, exact complete startup
tape equality after 57,922 transitions, dense/native conjugacy, and positive
duration constants at least 3. The scope covers arbitrary nine natural-number
register values, both decrement branches, arbitrary nonempty finite spare
lists, and arbitrary additional header gap. It uses no arithmetic-box oracle.

The complete suite also replayed the incoming packet's narrower historical
novelty comparison against its 82 representative classes, with two nonspanning
diagnostics excluded by invariant. That inherited comparison scope is distinct
from the fresh 110-class novelty audit of the new constructions.

The portable deliverable retains selected fresh logs and receipts under
`base_replay/quick/` and `base_replay/full/`, including both full independent
literal receipts and the final aggregate summary. Neither finite suite checks
the full new arithmetic derivation or provides an executable implementation of
the entire forward PA proof compiler. The summary explicitly records
`kernel_checked=false` and `arithmetic_derivation_checked_by_this_script=false`.

Recommended attribution in a new report: the construction may compose its own
explicit iPRA-preservation argument with the **latest incoming written AX11H
calibration**, while explicitly stating that no end-to-end Lean/Rocq proof of
the new result has been compiled. If a report elects not to rely on this
written calibration, state the exact relative theorem and conditional
consistency transfer instead; do not conflate these two scopes.
