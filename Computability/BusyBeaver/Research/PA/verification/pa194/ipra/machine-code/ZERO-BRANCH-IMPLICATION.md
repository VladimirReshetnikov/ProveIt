# Native iPRA implication for the site-25 zero branch

`PA194ZeroBranchImplication.nativeImplication` is an actual theorem of the
repository's native `IPRAStandardTheory.standardTheory`. It universally closes
the object-language implication: if original logical register 8 is zero, the
literal stepper applied to the canonical path-25 packed input at the selected
clock equals the explicit control-24, left-1, path-27 output with the complete
unchanged original source file and arbitrary suffix. `zeroTarget` in the source
is the exact primitive-recursive output term, and the stepper term is the
already checked canonical-input unified theorem's left-hand side.

The proof first establishes the stronger open disjunction: the register is
nonzero OR the specified equality holds. Its semantics uses the coherent
all-model unified step and output specification, for every candidate-PRA model,
then completeness yields the classical PRA sentence. The separately checked
`PA194OpenFormulaTransfer.nativeOpenOfClassical` uses the existing GG transfer
and bounded backward comparison to reflect any universally closed open
classical PRA formula to its native iPRA translation. Finally, intuitionistic
logic derives the stated implication from the native disjunction. The Lean
axiom audits for the transfer, model/classical/native disjunction and native
implication show only `propext`, `Classical.choice`, and `Quot.sound`; no
`sorryAx`. These Lean metatheoretic axioms are not object-theory axioms.

This is a native machine-step implication, not a consistency/nonhalting
implication or a model-length source-controller simulation.

## Staged replay

`check-zero-branch-implication.sh` pins and recompiles `PA194UnifiedOutputSpec`,
`PA194OpenFormulaTransfer` and `PA194ZeroBranchImplication` in one fresh output,
with printed axiom audits. It uses the separately built coherent PA194 machine
root, two prebuilt general logic roots and ordinary Lake/Mathlib objects; it
pins the coherent manifest and three direct objects but does not independently
rebuild or authenticate that entire baseline. In particular, the startup/header
baseline and general logic foundations remain explicitly staged prerequisites
of the coherent build. Paths shown are session-local.

From the repository root:

```sh
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
bash "$base/check-zero-branch-implication.sh" \
  "$PWD" "$base" \
  /dev/shm/pa194-unified-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker rejects inherited Git internal overrides and does not set them.
