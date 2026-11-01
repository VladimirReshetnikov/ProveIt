# Strict ZFC axiom-witness closure

The frozen nine-module suffix compiles the four actual ZFCinPA theory/scheme
modules after `Instances`, then `PRAWitnessBoundTerms`, `PRAWitnessSubsts`,
`PRAWitnessPR`, `PRAWitnessZFCAxioms` and its axiom check. Its theorem
`goodCh_zfc` supplies the axiom recognizer witness bounds in both polarities.
The source, object and log hashes match the independent nine-module replay.

```
python3 Computability/DiophantineConsistency/reviews/pra-zfc-witness-closure-replay/replay.py
```

The parent is the independently replayed 214-module frozen local-project
closure. The script guards all 214 parent project objects, the nine frozen
sources and 19 direct external object anchors, and rejects errors, warnings
and `sorryAx`. `ZFCinPA.Instances`, Foundation, toolchain, mathlib and other
package transitive object ancestry are inherited; source snapshots may cease
to match later workspace changes. This is the axiom-recognizer endpoint, not
the full derivation-core or PRA-equivalence theorem.
