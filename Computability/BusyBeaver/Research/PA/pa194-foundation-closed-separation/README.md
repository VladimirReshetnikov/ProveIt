# PA194 source separation with a closed parameter

`closedSeparationSupplier` supplies a finite PA194 proof of the translated
source separation formula universally closed over its first free parameter.
For any source property `p` and assignment `f`, it assumes `0 < lo`,
`∀ i, f i < lo`, and `lo + 4 + depth p ≤ z`. It uses the checked general
source-separation supplier and an explicit parameter-allocation identity;
the pinned upstream argument is adapted to the current Foundation API.
Its printed axiom dependencies are `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`.

This ordinary Lean result is one source-theory supplier for graph restriction
and arithmetic coherence. It does not prove the PA interpretation or a
PA-refutation reduction, machine nonhalting, or internalization in PA/PRA.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited Lean
4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-foundation-closed-separation/check.sh`.
The script rebuilds the nested source-separation prerequisites in tmpfs,
checks the upstream pin and rejects `sorryAx` in the axiom reports. The new
module has passed an overlay check; the full standalone script has not yet
completed.
