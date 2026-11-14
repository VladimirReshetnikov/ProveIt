# PA194 uniform ordinal-source induction supplier

For any current-Foundation source semiformula `p` with one bound variable,
`inductionFoundationDerivation p` is a concrete current Foundation LK proof
of the upstream ordinal-source induction statement
`inductionBase p → inductionStep p → inductionConclusion p` from the paid
exact-graph context, the fixed intersection axiom, and separation for `¬p`.
The proof adapts the pinned upstream minimum-counterexample and finite trace
arguments; it retains every free parameter of `p`.

`inductionSupplier` pays those source assumptions with already checked PA194
suppliers and compiles the constructed Foundation derivation. For any
assignment `f`, it constructs a finite PA194 proof of the translated
statement, assuming exactly `0 < lo`, `∀ i, f i < lo`, `lo + 6 < z`,
`lo + 3 + depth (∼p) ≤ z`,
`lo + 2 + foundationBudget foundationAdjunctionDerivation ≤ z`, and
`lo + foundationBudget (inductionFoundationDerivation p) ≤ z`. Both budgets
refer to concrete Foundation derivations. The printed axiom reports are
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This is source-ordinal induction in ordinary Lean. It does not yet establish
addition totality or the full PA interpretation, translate PA refutations,
prove machine nonhalting, or internalize the construction in PA/PRA.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-induction/check.sh`.
The script rebuilds the nested addition-step prerequisites in tmpfs, checks
the pinned source files and rejects `sorryAx` in printed axiom dependencies.
The new modules have passed an overlay check; the full standalone script has
not yet completed.
