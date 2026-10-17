# Numeric history checker for C254

`Code254History.lean` replaces proof-tree parsing during evaluation with a history of natural-number values. An invalid code has value0; a valid code has value one plus its conclusion. The initial history contains the value for code0, and each successor appends the value of the next code.

The twelve numeric rule rows preserve the original calculus, including MP's exact formula comparison and both bundle disequalities. Every recursive child index is at most the payload and therefore smaller than its enclosing positive node. `history_lookup` proves that every completed entry agrees with every depth-budget evaluator whose budget exceeds that entry's code. `accepts_iff_check` then proves agreement with `Code254Proof.check` for **all** natural-number inputs, including malformed or invalid proofs. Consequently `c254_iff_history` characterizes the same C254 relation by existence of an accepted history code.

This is an ordinary-Nat Lean construction. It provides the evaluator targeted by [the arithmetic construction plan](code254_arithmetic_checker.md), but does not yet give an arithmetic formula, an internally total PA function, or a PA consistency theorem. History construction here uses lists and appends; no efficiency claim is made.

Pinned Lean4.32.0 checked the module and eight concrete valid/invalid cases, three generic callers and eleven axiom reports. Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` occurred. The acceptance theorem inherits classical dependencies from the existing parser/quotation library; this does not supply an internal arithmetic correctness proof. The original calculus and numeric coding remain attributed to Mira-Cult and Jeff through the imported `Code254Proof`/`Code254` modules.

Reproduction metadata, the full caller source and axiom output are in [the verification record](results/code254-history-verification.json).

## Intake156 sparse continuation

Source48, reconciled in the
[closure-kernel report](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-156-source-48.md),
gives an ordinary all-input sparse evaluator for this same base12 calculus.
Its canonical dependency history has at most `floor(sqrt(3b+1))` rows for input
bit length `b`, including the zero row. The matching-order example concerns
unfolded occurrences, not distinct cached rows; accepted histories can contain
redundant correct rows. Explicit acceptance/rejection arithmetic graphs retain
all twelve tags, equality and guarded theory bundles. These are new ordinary
bounds, not a Lean sparse-history theorem or a complete cheaper binary search.
The checked dense all-code equality above remains the concrete comparison
target for a future sparse port.
