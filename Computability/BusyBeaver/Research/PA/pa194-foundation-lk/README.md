# PA194 compiler for current Foundation LK

`compileFoundationLK` consumes an actual `LO.FirstOrder.Derivation` in the
current Foundation library, for its membership/equality source language,
and constructs a finite PA194 calculus context proof of its translated
sequent. It handles Foundation's list-based sequents, generalized contraction,
and both quantifier rules. The theorem requires `0 < lo`, a label assignment
`f` with `f i < lo`, and `lo + foundationBudget d ≤ z`. The budget is
computed from the actual derivation and reserves fresh variable names.

`compileFoundationContext` specializes this to a finite source list: given
a Foundation derivation of the conclusion from the negations of those source
assumptions, and finite PA194 proofs supplying each translated assumption,
it produces a finite PA194 proof of the translated conclusion. Both printed
axiom reports are `[propext, Classical.choice, Quot.sound]`; there is no
`sorryAx`.

These are ordinary Lean theorems. They do not yet provide the relevant PA
axiom suppliers or a PA-refutation translation, prove nonhalting, or
internalize the compiler in PA/PRA. Unlike the earlier locally ported
multiset LK interface, the input here is the checked current Foundation
`Derivation` type. The result still uses the local compiler's checked
multiset-context lemmas internally.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation object directory and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-lk/check.sh`. It
rebuilds the nested source-context prerequisites in tmpfs and rejects
`sorryAx` in printed theorem dependencies. This new module has been checked
against independently rebuilt prerequisite overlays; the full standalone
script has not yet completed.
