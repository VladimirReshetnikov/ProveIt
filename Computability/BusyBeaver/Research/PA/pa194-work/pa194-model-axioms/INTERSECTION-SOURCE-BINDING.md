# Source intersection sentence and its target axiom leaf

`sourceIntersection` is the universally closed sentence obtained from the existing `PA194SourceIntersection.Ordinal.intersectionFormula` using `.univCl`. `intersection_coe` proves that embedding this sentence back into the free-variable source language gives exactly `Ordinal.intersectionFormula`. `intersection_quote` proves that its model-valued quote equals the explicit closed atomic separation code `∀ sepRoot(bvar 0 ∈ bvar 3)`. Thus `intersection_axiom` applies the independently checked atomic separation leaf to the actual quoted source intersection sentence. Its hypotheses are source sequent validity, membership of that quote in the sequent, and SeedAdmission at its actual axiom node. The model satisfies PRA and IΣ₁; the three theorems have axiom reports `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

This connects one fixed intersection axiom to the numerical target compiler; it does not establish arbitrary parameterized separation, a complete PA interpretation, a native iPRA derivation, or any consistency equivalence.

The independent source-suffix replay exited 0 in `/tmp/pa194-intersection-source-binding-replay.log`. It checks the new source, the existing `PA194SourceIntersection.lean` hash, and two selected source-built prerequisite object hashes before and after compilation; other transitive baseline and workspace/foundation objects remain prebuilt and are not independently authenticated by these checks. This is not a clean whole-workspace build.

From the repository root, use a fresh output path:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-intersection-source-binding.sh "$PWD" /dev/shm/pa194-atomic-parameter-separation-replay-v2 /dev/shm/pa194-one-parameter-separation-replay /dev/shm/pa194-ranked-open-separation-replay-v3 /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-full-one-level-audit /dev/shm/pa194-intersection-source-binding-replay
```
