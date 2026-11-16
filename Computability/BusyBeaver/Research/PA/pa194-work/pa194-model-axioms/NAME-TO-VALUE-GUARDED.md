# Guarded name-to-value extraction

`PA194NameValueSchema.nameToValueGuarded` proves the exact guarded sequent `¬tr(exName s), ∃v valBody(s)[v]` for every internally valid arity-zero PAeq term `s` and any Δ₁ source theory, including nonstandard term codes. It uses the independently replayed `nameToValue` source-provability theorem and the existing typed disjunction inversion rule. It assumes no source axioms, other naming fields, or value-existence premise.

From the repository root, with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-name-to-value-guarded.sh "$PWD" /dev/shm/pa194-name-to-value-guarded-repo
```

The checker recompiles the module against the independently source-replayed `/dev/shm/pa194-name-to-value-repo`, the repository-built name-forms/Schematic baseline and other prebuilt objects listed in the script, including Foundation. It requires one clean axiom report and rejects `sorryAx`. The result is uniform over IΣ₁ arithmetic models; it does not show that a value or name exists, discharge `eSucc`, or prove a native iPRA theorem.
