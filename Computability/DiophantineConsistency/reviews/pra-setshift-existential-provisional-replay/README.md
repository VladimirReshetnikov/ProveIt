# General setShift existential bound on a provisional parent

The new theorem gives `WB M (∃⁰ ψ)` for a sigma-one body `ψ` with `WB M ψ`,
provided that in every model of `IΣ₁`, each witness to `ψ` satisfies the actual
set-language `setShiftGraph` at a specified index of its input valuation. The
index and arity are arbitrary. It obtains a concrete exponential bound via
`setShift_le` and transfers it to candidate-PRA models; it does not assume
candidate-PRA models satisfy `IΣ₁`. This is a general rule for the applicable
quantifiers, not yet a proof of the specific enclosing derivation rule.

Both axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.
Run from the repository root:

```
python3 Computability/DiophantineConsistency/reviews/pra-setshift-existential-provisional-replay/replay.py
```

The script rebuilds the theorem and checks, guarding 220 declared project
sources and 218 inherited project objects. The parent
`/tmp/pra-setshift-coherent/lib` contains the independently replayed 102-source
set-term history parent and a freshly compiled witness chain. Other inherited
project source/object correspondence and Foundation, ZFCinPA and package
provenance are not authenticated. The witness parent emitted an upstream
unused-section-instance linter warning in `PRAWitnessSetTerms`, so this is not
a strict warning-free rebuild of its whole closure.

The independent replay `/tmp/pra-setshift-existential-independent-4f9bu3v8`
passed and matched both source/object/full-log hashes. Its state and logs are
frozen in `independent-evidence/`; the same inherited-provider and explicit
body/graph premises remain.
