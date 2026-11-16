# NameFacts assembly from 11 remaining fields

`NameFactsRemainingEleven` lists the 11 still-assumed fields after removing six whose source proofs are available: `nRefl`, `nameOfUniq`, `uVar`, `uZero`, `eVar`, and `eZero`. `fullSource_nameFacts_of_eleven_fields` supplies these six checked fields and constructs the full `NameFacts` structure from the other 11.

This is a model-level candidate-PRA plus arithmetic-IΣ₁ theorem. The 11 remaining fields, the native iPRA transfer, and the PA194 machine equivalence are not established here.

The checker rebuilds both source modules and verifies source and direct repository object hashes; transitive dependencies remain prebuilt. From the repository root run:

```
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-name-facts-eleven.sh "$PWD" /dev/shm/pa194-name-facts-eleven-repo-NEW-NEW
```

Both printed axiom reports omit `sorryAx`.
