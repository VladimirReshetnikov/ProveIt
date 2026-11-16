# Conditional ordinary-PAeq refutation transfer

`refutation_of_eleven` composes the six-field NameFacts assembly, the generic NameFacts-to-TermFacts theorem, and the existing four-case interpretation. Given an internal ordinary-PAeq refutation, it derives a full-source refutation under three explicit remaining premise groups: the other eleven naming fields, four fixed-axiom translations, and every translated induction instance. All are quantified over the ambient candidate-PRA model with arithmetic IΣ₁.

This is conditional and model-level. It does not discharge those premise groups, prove the corresponding implication in native iPRA, or establish the PA194 machine equivalence.

The checker rebuilds this module and verifies its source and direct repository object hashes; transitive dependencies remain prebuilt. From the repository root run:

```
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-name-refutation-eleven.sh "$PWD" /dev/shm/pa194-name-refutation-eleven-repo-NEW-NEW
```

The printed axiom report omits `sorryAx`.
