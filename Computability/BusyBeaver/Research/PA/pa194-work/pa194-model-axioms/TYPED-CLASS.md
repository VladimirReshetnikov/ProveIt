# Typed characterization under quotation surjectivity

`fullSepUniform_typed_of_surjective` proves that, in a PRA plus IΣ₁ model, the numeric full-separation classifier recognizes exactly the quotes of `(separationFormula p).univCl` for typed arity-one properties p, **if every internally valid arity-one code in that model is a quote of such a typed property**. This hypothesis is explicit and should not be assumed for arbitrary nonstandard models. The theorem uses the exact typed quotation bridge and the replayed classifier interpretation.

Run from the repository root with a fresh final output path:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-typed-class.sh "$PWD" \
  /dev/shm/pa194-typed-schema-replay \
  /dev/shm/pa194-full-sep-theory-replay \
  /dev/shm/pa194-typed-class-replay
```

This staged replay pins the source and two key imported objects; other overlays and Foundation are prebuilt. Successful log: `/tmp/pa194-typed-class-replay.log`. A full standard-theory identity still requires connecting canonical Nat quotation/decoding with the candidate-PRA-induced Nat operations.
