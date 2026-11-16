# Native iPRA implications for both site-25 branches

`PA194ZeroBranchImplication.nativeImplication` and
`PA194PositiveBranchImplication.nativeImplication` are actual universally
quantified implications proved in native `IPRAStandardTheory.standardTheory`:

* If original logical register 8 is zero, applying the literal stepper at the
  selected clock to the canonical unmodified path-25 input yields the exact
  packed path-27 output with the complete unchanged source file.
* If that register is not zero, the same canonical-input/selected-clock
  literal step yields the exact packed path-26 output with the complete source
  file updated only at register 8 to its primitive-recursive predecessor.

All other logical registers, the spare and numeric suffix are arbitrary. Both
formulas are explicit object-language implications. Their exact terms,
including zero-run lengths and selected clock, are defined in the Lean source.

The proof first obtains open native disjunctions from their all-model
interpretations by classical PRA completeness and the reusable checked
`PA194OpenFormulaTransfer.nativeOpenOfClassical`, then derives each implication
in native intuitionistic logic. The model statements, classical PRA proofs,
native disjunctions and native implications print only Lean's `propext`,
`Classical.choice`, and `Quot.sound`, without `sorryAx`. These are metatheoretic
Lean assumptions, not extra object-theory axioms. The results are finite
machine-step implications, not either direction of PA consistency versus
nonhalting and not a full model-length source-controller simulation.

## Staged replay

`check-branch-implications.sh` pins and recompiles the unified output
specification, the open-formula transfer and both branch-implication modules in
one fresh output and audits the printed axiom lists. It uses the separately
built coherent PA194 machine root, two prebuilt general logic roots and ordinary
Lake/Mathlib objects. It pins that coherent manifest and three direct objects,
but does not independently rebuild or authenticate all of the baseline or its
transitive foundations. The prior startup/header and general logic foundations
remain explicit staged prerequisites of the coherent build; the example roots
below are session-local.

From the repository root:

```sh
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
bash "$base/check-branch-implications.sh" \
  "$PWD" "$base" \
  /dev/shm/pa194-unified-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker rejects inherited Git internal overrides and does not set them.
