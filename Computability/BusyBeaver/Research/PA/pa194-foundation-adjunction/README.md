# Exact adjunction supplier for PA194

`foundationAdjunctionDerivation` is an actual current Foundation LK
proof of the source adjunction instance from the five explicit source
premises assembled in `pa194-source-context`: weak adjunction, a separation
instance, and equality reflexivity, symmetry and congruence. The proof
constructs both existential witnesses through the LK eigenvariable rule,
derives equality transport, and adapts the pinned upstream source proof to
current Foundation and its list-based natural-deduction interface.

`foundationAdjunctionSupplier` composes that fixed Foundation derivation
with the already proved PA194 premise suppliers and current-Foundation LK
compiler. For any assignment `f`, it constructs a finite PA194 calculus
proof of the translated universally closed exact-adjunction formula. It
assumes exactly `0 < lo`, `lo + 6 < z`, and
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`. The last
bound refers to a concrete constructed derivation, not an assumed source
proof. Both axiom reports are `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`.

`emptySupplier` additionally gives a finite PA194 proof of the translated
empty-set axiom for any assignment `f`, assuming `lo + 1 < z`.

This result is an ordinary Lean construction. It does not by itself
supply the rest of a PA interpretation, translate PA refutations, prove
candidate-machine nonhalting, or formalize any reduction inside PA/PRA.
The source hashes identify the adapted upstream arguments and do not assert
that the two Foundation versions are definitionally equal.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation object directory and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-adjunction/check.sh`.
The script rebuilds the complete Foundation-ND prerequisite chain in tmpfs,
checks the upstream pins and rejects `sorryAx` in printed axiom dependencies.
The seven new modules have passed an overlay check; the full standalone script
has not yet completed.
