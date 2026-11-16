# NameFacts assembly with variable and zero existence

`NameFactsWithoutBaseExistence` lists exactly the 15 fields of `NameFacts` other than `eVar` and `eZero`. The generic assembly theorem adds those two fields as explicit premises. `fullSource_nameFacts_of_other_fields` discharges both from the existing full-source model-level proofs and thus constructs `NameFacts` from the remaining 15 fields.

The remaining fields, including `uVar`, `uZero`, and the function-layer cases, are still assumptions. This is a candidate-PRA-model plus arithmetic-IΣ₁ theorem, not a native iPRA proof or a machine-halting equivalence.

The checker rebuilds both source modules in a fresh output and verifies direct source/object SHA-256 pins; transitive imports remain prebuilt. Run from the repository root:

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-name-facts-base.sh "$PWD" /dev/shm/pa194-name-facts-base-repo-NEW-NEW
```

Both printed axiom reports omit `sorryAx`.
