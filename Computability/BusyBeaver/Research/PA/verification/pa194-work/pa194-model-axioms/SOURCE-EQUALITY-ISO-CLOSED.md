# Closed standard equality-to-isomorphism derivation

`eqIsoClosedProof` universally closes the checked open source derivation, proving `∀a b c, domain(b) → domain(c) → b=a → c=a → orderIso(b,c)` from explicit source equality and isomorphism-reflexivity proof parameters. `shiftRefl` preserves the closed reflexivity proof through eigenvariable shifts.

This is a standard natural-deduction derivation with two explicit proof parameters. It does not yet discharge those assumptions in the full source theory, identify the formula with the `SourceFacts.ei` schema, or establish an internal iPRA or machine result. The checker rebuilds this module and checks source/direct dependency pins; transitive dependencies are prebuilt.

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-source-equality-iso-closed.sh "$PWD" /dev/shm/pa194-source-equality-iso-closed-repo
```

Both printed axiom reports omit `sorryAx`.
