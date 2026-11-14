# Natural-deduction rules for current Foundation LK

This file constructs a finite natural-deduction interface whose proof terms
are actual `LO.FirstOrder.Derivation` values. It supplies assumption,
weakening, modus ponens, implication introduction, conjunction and
disjunction introductions and eliminations, contradiction, and universal
and existential introductions and eliminations. The checked
`pa194-foundation-lk` compiler can consume these Foundation derivations.
The axiom reports show no `sorryAx`.

This interface supports constructing the missing adjunction derivation; it
does not itself supply that derivation, a PA-refutation translation, or an
internal PA/PRA proof. Its rules adapt the pinned PA196 source natural-
deduction design to current Foundation's list-based LK calculus.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-nd/check.sh`. The
script rebuilds the full Foundation-LK prerequisite chain in tmpfs and checks
printed axiom dependencies. The module has been checked against rebuilt
prerequisite overlays; the full standalone script has not yet completed.
