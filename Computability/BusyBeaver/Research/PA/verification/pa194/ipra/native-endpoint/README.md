# The native iPRA equivalence for literal PA194

`PA194NativeLiteralFinal.consistency_iff_literal_nonhalt` has type

```lean
standardTheory ⊢ nativePAConsistency 🡘 ∼PA194ExplicitEndpoint.haltSentence
```

This is a derivation in the repository's iPRA proof system. It has no
machine-specific hypothesis. The halting sentence uses the given literal
194-state table on blank input. Its table hash is
`4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`.

The arithmetic calibration supplies internal PA refutations from a scheduler
halt and conversely yields a scheduler halt from an internal PA refutation.
The [literal machine proof](../machine-code/ax-controller/README.md) identifies
scheduler halting with that literal halting sentence in the covered models.
The theorem combines the model results using the existing transfer to iPRA.

Run the following staged check from the repository root with the pinned
lower inputs available.

```sh
dir=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/native-endpoint
bash "$dir/check-literal.sh" "$PWD" /dev/shm/pa194-native-literal-final-new
```

The check verifies the literal table, selected source and direct object
hashes, then recompiles the final theorem and audits its axioms. Lean
reports `propext`, `Classical.choice`, and `Quot.sound`. The check retains
the staged Foundation, arithmetic and machine objects. The order of the
lower stages matters when several build outputs contain the same module.
The other check scripts replay the arithmetic calibration, its native
endpoint, and the independently stated scheduler/refutation result.
