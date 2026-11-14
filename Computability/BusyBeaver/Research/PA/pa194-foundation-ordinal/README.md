# PA194 ordinal-domain inhabitation

`emptyFoundationDerivation` is an actual current-Foundation LK proof that
empty-set existence implies inhabitation of the upstream relational ordinal
domain. The domain includes transitivity, member transitivity and linearity,
internal extrema, and member irreflexivity; no external finiteness or
extensionality assumption is introduced. Its source syntax and finite LK
proof adapt the pinned upstream ordinal-domain and empty-representative
files to current Foundation and the checked natural-deduction interface.

`inhabitedSupplier` composes that derivation with the checked PA194 empty-set
supplier and Foundation LK compiler. For assignment `f` it constructs a
finite PA194 proof of the translated inhabited-domain formula, assuming
`0 < lo`, `∀ i, f i < lo`, `lo + 1 < z`, and
`lo + foundationBudget emptyFoundationDerivation ≤ z`. The budget refers
to the concrete constructed Foundation derivation; no source-proof premise
remains. The printed axiom reports are `[propext, Classical.choice,
Quot.sound]`, with no `sorryAx`.

This is one ordinary Lean component of the PA interpretation. It does not
by itself translate PA refutations, establish machine nonhalting, or
internalize the proof in PA/PRA.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-ordinal/check.sh`.
The script rebuilds the complete Foundation-adjunction chain in tmpfs, checks
and builds the pinned source-intersection module in that same overlay, and
checks the three ordinal modules and their printed axiom dependencies. The
new modules have passed an overlay check; the full standalone script has not
yet completed.
