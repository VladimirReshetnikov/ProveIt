# Internal validator equality laws

`ValidatorEqualityCore254` derives equality reflexivity, symmetry, transitivity,
and congruence in both coordinates of equality and membership for arbitrary
internal labels in every model of IΣ1. These are finite proofs using the actual
CProv rule closures and the checked quantifier interface.

Reflexivity chooses the fresh label x+1. The proof uses both original atomic
vacuity gates, existential equality, and existential elimination. The resulting
laws include zero and coincident labels; no constructor injectivity, formula
renamer, or renaming closure of accepted proofs is assumed.

The source and audit passed on the first attempt: nine named axiom probes,
twelve callers, only `propext`, `Classical.choice`, `Quot.sound`, and zero warnings.
The guard reused 21 project source/object pairs, three direct external boundaries
and the explicit Seq anchor, plus actual Init/Omega. All 62 proof inputs and the
fresh object were checked before/after; its hash was recorded before the audit.
The run used one thread, 4096 MiB, default options and a 120-second command bound.
No prerequisite was rebuilt or downloaded.

The portable guard is byte-identical to the executed guard. Its maintained-default
preparation made no compiler or version call. The child review covers the original
source and audit; the root reviewed the guard and successful kernel evidence.
Exact evidence, source/driver snapshots and review scopes are recorded separately.

```sh
python Logic/Interpretability/ZFCinPA/check_validator_equality_core254.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --output /external/fresh/equality-check
```

These lemmas supply the atomic step of a future environment comparison.
The internal formula induction, ZF axiom clients and source-proof compiler remain
open; this checkpoint proves no reverse consistency or binary-machine endpoint.
