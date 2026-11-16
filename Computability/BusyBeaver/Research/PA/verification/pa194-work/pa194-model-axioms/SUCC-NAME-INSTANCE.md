# Source instance of the successor-name uniqueness schema

`sourcePredicates s hs` instantiates the schematic P, E and S letters with the actual internal translated term-value formula `valBody s`, ordinal-isomorphism formula `orderIsoCode` guarded by domain membership on both arguments, and output-domain-guarded `successorCode`. The construction accepts any valid internal term code s, including nonstandard ones. `sourceInstance_provable` proves the corresponding schema instance in every Δ₁ internal source theory.

This is an implication, not the `uSucc` field. The translation of its name predicates to the exact `tr (uniq s)` / `tr (uniq (succT s))` formulas, and source derivations of the original-name uniqueness, value-selfhood, guarded-isomorphism symmetry/transitivity, and successor-coherence premises, remain to be established. It does not establish a native iPRA statement or a machine equivalence.

The checker rebuilds this source and verifies source/direct object pins; transitive dependencies are prebuilt. From the repository root:

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-succ-name-instance.sh "$PWD" /dev/shm/pa194-succ-name-instance-repo
```

The printed axiom report omits `sorryAx`.
