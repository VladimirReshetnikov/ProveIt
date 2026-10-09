# Proposed ProveIt integration

Baseline reviewed: `3a90fb34146c915328ab8eac6250cc2514f74ed0`.

This is an additive research package, not a patch to `fastunknot` or to any production recognition default. Suggested placement is a new descriptive report directory, for example:

```
Topology/UnknotRecognition/research/disc_completion_bases/
```

Preserve the delivered archive in `docs/incoming` according to the existing intake instructions, and choose the repository's next report number only during intake. No existing path or report number is assumed free by this delivery.

The most direct integration point is a candidate-family boundary in a **geometric disc-assembly search**, after constructing and verifying partial surfaces with a uniform source-bound collar interface. It is not the existing module whose name contains `disk_transfer`: that module works with Khovanov algebra, and minimum/existence representatives do not preserve its homology data.

## Required review gates

1. Reproduce `make test`, `make audit`, and `make check-example`; inspect source hashes and the theorem dependency map.
2. Independently review the topology contract and the grade-sensitive rank proof. Compare with the prior acyclic-representative theorem rather than describing the whole method as novel.
3. Implement a source-bound geometric exporter. Bind each candidate ID to exact witness bytes, component ownership, embedding evidence, and the input knot/exterior. A table SHA-256 alone is insufficient.
4. Prove that all future pairing constraints are uniform within each `control` type. Include exact boundary germs, gluing maps, external trace, and any normal admissibility data. Charge the number and encoding size of controls.
5. Count individual exposed interval copies. Do not substitute the number of compressed port labels for that count without a new theorem.
6. Run native differential tests on actual geometric candidate families, preserving the existing exact backend. Include source construction, preprocessing, output size, independent checking, and end-to-end time, with low-reuse and no-compression controls.
7. Prove a complete generator and total width/type/search bound before making a global quasi-polynomial claim. Resource failures stay inconclusive.

**Native integration gate status: UNEXECUTED.** No native source adapter or native timing result is represented as executed in this package. The delivered staged joins are algebraic partition tests only.

## Safe incremental adoption

The reducer can first run in shadow mode on bounded exported families. Keep all original candidates, compare every requested completion optimum against both tables, and archive counterexamples. Shadow-mode success is evidence for the exporter and local contract, not proof of universal geometric coverage. A release should enable deletion only after the uniformity theorem and source binding are reviewed.

There is no patch replacing the existing exact-state census: exact online observations and objective-specific family selection solve different problems. Keep both interfaces named distinctly.
