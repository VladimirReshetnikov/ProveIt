# Contextual quantifier proof codes

These sources give fixed parameter-free Σ₁ arithmetic graphs, actual internal proof constructors, and exact output-code equations for universal introduction and existential elimination under an arbitrary internal context. They work model-by-model for the covered candidate PRA models with IΣ₁ arithmetic reducts, any internal source theory, and arbitrary valid model-valued formulas and proofs, including nonstandard values.

Universal introduction takes a proof of the opened body under the shifted context. Existential elimination takes a proof of the existential and a proof of the negated opened body under the shifted context extended by the shifted conclusion; the shifted context is essential for the eigenvariable condition. Both premises are explicit hypotheses. Neither constructor establishes the ordinal induction sequent or a native iPRA theorem.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-quantifier-code.sh "$PWD" /dev/shm/pa194-context-quantifier-code-replay
```

Both sources are rebuilt into one output. The checker verifies source and direct dependency hashes, lists additional prebuilt dependency directories, and rejects sorryAx; all six axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.
