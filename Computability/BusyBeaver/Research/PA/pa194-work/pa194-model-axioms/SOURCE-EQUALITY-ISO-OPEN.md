# Open source derivation from equality to isomorphism

`eqIsoAt` is a standard source natural-deduction proof for arbitrary standard free-variable indices a, b, c: from source equality axioms and the closed theorem `∀x (domain(x) → orderIso(x,x))`, it proves `domain(b) → domain(c) → b=a → c=a → orderIso(b,c)`. It uses equality symmetry/transitivity and substitution into the order-isomorphism formula.

Both equality and isomorphism-reflexivity proofs are explicit parameters. This open standard derivation is not yet the closed `SourceFacts.ei` supplier: universal closure, source-axiom discharge, the `sEI` quotation identity, and internal model-level transfer remain to be supplied. It is not an iPRA or machine theorem.

The checker rebuilds the source and verifies direct pins; transitive imports are prebuilt. From the repository root run:

```
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-source-equality-iso-open.sh "$PWD" /dev/shm/pa194-source-equality-iso-open-repo
```

The printed axiom report omits `sorryAx`.
