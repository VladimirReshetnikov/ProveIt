# Candidate-PRA setShift graph bound on a provisional parent

`PRAWitnessSetShiftCandidate.wb_setShiftGraph` establishes a monotone witness
bound for Foundation's actual `setShiftGraph ℒₛₑₜ` in arbitrary candidate-PRA
models. It discharges the earlier shift-graph hypothesis using
`PRAWitnessFormulaFunctions.wb_shiftGraph`. The axiom check reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Run from the repository root:

```
python3 Computability/DiophantineConsistency/reviews/pra-setshift-candidate-provisional-replay/replay.py
```

The script rebuilds the candidate theorem and checks, guarding 216 declared
current project sources and 214 inherited project objects before and after.
The parent `/tmp/pra-setshift-coherent/lib` includes the independently
replayed 102-source set-term history parent and a freshly compiled witness
chain, but other project source/object correspondence and Foundation,
ZFCinPA and package provenance remain inherited. The parent build emitted an
unused-section-instance linter warning in `PRAWitnessSetTerms`; this is not a
strict, warning-free rebuild of the whole closure. The result also does not
bound the separately quantified setShift output or finish a derivation core.

The independent replay `/tmp/pra-setshift-candidate-independent-yeuh3ijc`
also passed, with matching source/object/full-log hashes for both modules.
Its state and logs are frozen in `independent-evidence/`; it uses the same
partially inherited parent and does not resolve the warning or output bound.
