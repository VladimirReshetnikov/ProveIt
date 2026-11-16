# Uniform ordinal base application proof code

The two sources define fixed parameter-free Σ₁ arithmetic graphs for a contextual base-application proof constructor, generically and for the actual ordinal-domain and zero templates. For every covered candidate PRA model whose induced ordered ring models IΣ₁, every internal Δ₁ theory, valid internal arity-one property, internal term or index and internal context, the proof constructors consume actual internal derivations of the base formula, domain instance and zero instance and return an internal derivation of the property instance. The `_val` theorems identify the output proof code with the graph's function, including for nonstandard inputs.

This is a conditional proof-code construction: the three input derivations remain hypotheses. It does not derive the ordinal induction sequent, identify PA with the source theory, or establish a native iPRA theorem.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-base-code.sh "$PWD" /dev/shm/pa194-ordinal-base-application-code-replay
```

The checker replays both source files in one output directory and checks SHA-256 hashes for these sources and three direct prebuilt dependency objects; the script lists all remaining prebuilt dependency directories. The replay's axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`, and no `sorryAx`.
