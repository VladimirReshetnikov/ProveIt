# Four one-row 196-state variants

These are new search starting points, not solutions to the requested state-count target.

Let M be the published PA196 table at BusyBeaver commit 407cdc356f6b586635e71ac92be394255f4bfea4. The native row (1365,1), corresponding to dense row (193,1), implements the final AX `breakTo 1` at source PC3692. Its published action is native `0 L302`, dense `0 L131`.

Replace this one row as follows, leaving every other row and the start state unchanged:

| Variant | Tested logical register | Native action | Dense action |
|---|---:|---|---|
| close-CD3 | 3 | 1 R17 | 1 R17 |
| close-CD4 | 4 | 1 R144 | 1 R113 |
| close-CD5 | 5 | 1 R45 | 1 R44 |
| close-CD6 | 6 | 1 R21 | 1 R21 |

Every table still has196 working states and392 rows. All196 working states are reachable in the directed transition graph. Rooted action-preserving canonicalization distinguishes these four tables from each other and from the published machine. This graph reachability does not assert that every state occurs on the blank run.

## Correctness argument

The source program's final AX guard leaves registers3,4,5,6,7 zero. This is explicitly present *before* the final closing jump in the upstream file PA196/Source/AXGate.lean: its local proof `fifth` ends at PC3692 with store `(T,0,0,0,0,0,f)`, and `sixth` is the final one-step jump to3799. AXGateSteps.lean maps those five store fields to registers3,4,5,6,7. No uniform PA truth predicate or consistency assumption is involved in this arithmetic fact.

For any source address p, a zero conditional decrement CD(r) and a `breakTo 1` choose the same continuation: both discard through the innermost zero edge of p and proceed beyond that subtree. When register r is zero, CD(r) leaves the entire register file unchanged. Consequently replacing the closing source instruction by CD(r), for r=3,4,5,6, is a one-step semantic equality at every reachable occurrence of that PC. The source invariants for earlier instructions and the successor at3799 remain unchanged.

The physical change is checked against all4,959 primitive instruction contracts. Every ordinary contract is unchanged. For the closing instruction alone, the checker receives the proved side condition that its chosen register is zero. Each check uses a symbolic arbitrary-natural gap and the complete arbitrary register-file frame, with the same fixed register-engine macro lemmas as the upstream package. The engine rows are unchanged. All four checks return:

- contracts:4,959;
- maximum abstract execution steps:515;
- total abstract steps:1,619,855.

These abstract counts are not literal TM running times. Each complete blank startup is separately checked for58,154 literal steps and reaches exactly the published q84/head/tape seed. Thus all four new machines have the same blank-tape halting behavior as M, by the source invariant and physical simulation arguments. The relative equivalence can be formalized in PA by the same elementary finite-trace/list-loop argument used for the source simulation; no new end-to-end Lean endpoint is claimed here. Whatever PA-calibration theorem is available for M transfers through this relative equivalence; the upstream reverse internal consistency direction retains its separately stated proof status.

## Reproducible files

- `pa196_close_cd3.tm` through `pa196_close_cd6.tm`: contiguous labels0..195, terminal196.
- Corresponding `.native.tm` files: native labels, initial74, terminal254.
- `closing_patches.py`: regeneration, all4,959 constrained physical contracts, and exact startup comparison.
- `closing_patch_receipt.json`: row changes, counts, hashes and validation results.
- `closing_canonical_classes.json`: five distinct rooted transition-graph classes.

The earlier `close3_196.json` etc. recompile the same source layout with temporary AX labels2000+; those bulky discovery records are unnecessary in the final deliverable. Prefer the direct one-row tables above.

## Other new research

The source0/nonzero certificate has274,880 abstract states and326,688 abstract edges over3,812 PCs. `verify_zero_invariant.py` independently checks closure and the candidate2 seed. A source mask records exactly which of the nine registers are positive. An increment forces its bit on; a positive decrement allows either the zero or positive successor. This finite nondeterministic abstraction soundly overapproximates all concrete runs. The exact finite certificate yields a PA-provable inductive invariant by ordinary finite case analysis. It is not a new Lean kernel check.

The same232,848 one-row-fold tables were tested under successively stronger analysis of reachable source frames: Boolean masks; difference bounds; and their reduced product plus numerical intervals. These are repeated checks of one finite candidate family, not698,544 distinct machines. New tests permit repeated register-engine excursions, tracked integer offsets, extra spare registers and extra nonnegative gap growth. Protected register-engine rows must remain unchanged. The early unprotected files `zero_candidate_66_40.json`, `zero_candidate_66_54.json`, `zero_candidate_74_64.json`, and `zero_candidate_94_24.json` are explicitly rejected because the symbolic engine assumptions were not preserved; they must not be packaged as candidates.

Further bounded grammar searches jointly varied independent role names in the six axiom heads, head order, antecedent order, equality orientation and tree association. A stochastic search completed560 cycles of3,000 iteration slots; its minimum remained the baseline62 physical AX-reader states. Separate C++ stochastic RePair search examined300,000 metadata proposals with four parses each and reached70 raw grammar nodes, above the baseline68. A dictionary-assisted search of50 single-head/gate variants reached68 raw nodes but no lower effective physical cost. Inserting any of11 existing scratch-zero-loop no-ops before or after69 safe macro subtrees produced1,518 layouts, whose best estimated count was197. None supplies a state-count lower bound.
