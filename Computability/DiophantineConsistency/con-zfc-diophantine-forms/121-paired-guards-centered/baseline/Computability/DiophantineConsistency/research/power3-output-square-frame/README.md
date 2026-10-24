# Ordinary62 source: square the third power output in the frame

This separate successor to the accepted63 source appends raw106², uses it
only in frame row1152, and removes only scalar106's predicate. Actual call3
still outputs raw106. The source has1268 coordinates/1186 rows and the
guarded integer parent1454 coordinates/1248 rows with62 predicates.

[PROOF.md](PROOF.md) gives the complete acyclic ordinary proof and fresh
completeness. [FULL_SOURCE.md](FULL_SOURCE.md) records the unchanged arithmetic
and native interfaces. [CERTIFICATE.json](CERTIFICATE.json) records the six
delayed values, actual call3, independent supporting calls8/9, the delayed
bound130 and strict133, and all new frame ideals. SOURCE_PINS authenticates
the accepted source proofs and the exact five new basic prototype files.

The standalone checker imports no producer, optimizer, parent checker or
incoming code. It replays the ordered prefix and restored closure, collects
all actual arithmetic interfaces and both frame forms, verifies every
retained predicate/name/auxiliary mapping, and rejects actual corruptions.
Normal and optimized Python use explicit exceptions. No projected metric,
optional CSE, canonical page, common document or new Lean result is claimed.

```
python -B Computability/DiophantineConsistency/research/power3-output-square-frame/check.py --output /tmp/power3-ordinary-normal.json
python -B -O Computability/DiophantineConsistency/research/power3-output-square-frame/check.py --output /tmp/power3-ordinary-optimized.json
```
