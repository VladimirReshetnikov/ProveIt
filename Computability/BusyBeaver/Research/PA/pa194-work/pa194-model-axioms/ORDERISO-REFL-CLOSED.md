# Closed order-isomorphism reflexivity source proof

`PA194OrderIsoReflClosed.sourceProof` discharges the existing standard `orderIsoReflexivityDerivation` against its eight full-source axiom suppliers to obtain a typed source proof of the closed theorem `∀a (domain(a) → orderIso(a,a))`, in each candidate-PRA model whose arithmetic reduct satisfies IΣ₁.

It is an input to proving `SourceFacts.ei`, but this module does not derive `ei`, the other SourceFacts, or any native iPRA or machine statement. The checker rebuilds its source and pins direct prebuilt objects; transitive dependencies remain prebuilt.

```
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-orderiso-refl-closed.sh "$PWD" /dev/shm/pa194-orderiso-refl-closed-repo
```

The two printed axiom reports omit `sorryAx`.
