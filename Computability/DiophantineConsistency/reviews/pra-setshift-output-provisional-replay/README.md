# Set-shift output bound on a provisional parent

The project module defines the exact `BoundTerm` for the existing double
exponential setShift output majorant, verifies it in models of `IΣ₁`, and uses
witness transfer to prove `WB` of the negated pi functional graph of the actual
set-language `setShiftGraph` in arbitrary candidate-PRA models. This is a local
functional-graph theorem; the enclosing derivation-rule branch remains to be
assembled. Both axiom checks report only `propext`, `Classical.choice`, and
`Quot.sound`.

Run from the repository root:

```
python3 Computability/DiophantineConsistency/reviews/pra-setshift-output-provisional-replay/replay.py
```

The script rebuilds the theorem and checks, guarding 219 declared project
sources and 217 inherited project objects. The parent
`/tmp/pra-setshift-coherent/lib` includes an independently replayed 102-source
set-term history parent and a freshly compiled witness chain; other inherited
project source/object correspondence and Foundation, ZFCinPA and package
provenance remain unauthenticated. The upstream parent build emitted an
unused-section-instance warning in `PRAWitnessSetTerms`; this is not a strict,
warning-free rebuild of the whole closure.

The independent replay `/tmp/pra-setshift-output-independent-il3vjhoq`
passed with both source/object/full-log hashes matching the author. Its state
and logs are frozen in `independent-evidence/`; the same parent qualifications
and enclosing-rule obligation remain.
