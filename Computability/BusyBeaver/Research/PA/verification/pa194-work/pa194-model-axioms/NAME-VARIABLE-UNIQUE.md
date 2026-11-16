# Full-source uniqueness of variable names

`PA194GuardedCompiler.fullSource_uVar` proves the `NameFacts.uVar` field for the full source theory and every model-valued free-variable index, with no additional source-proof hypotheses. The replay rebuilds the equality-cancellation cut, the arithmetic quotation and all three openings of transitivity, the pointwise translated transitivity source sequent, and the final composition with the previously replayed pointwise symmetry.

The result is model-level under candidate PRA and an arithmetic IΣ₁ reduct. It does not discharge the remaining naming fields, prove a native iPRA statement, or establish the PA194 halting equivalence. The checker verifies the four source hashes and direct repository object pins; transitive dependencies are prebuilt.

From the repository root run:

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-name-variable-unique.sh "$PWD" /dev/shm/pa194-name-variable-unique-repo-NEW-NEW
```

All printed axiom reports omit `sorryAx`.
