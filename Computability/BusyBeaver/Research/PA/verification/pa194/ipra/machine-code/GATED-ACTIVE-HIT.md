# Gated physical halt and PR-code hit: conditional composition

`PA194GatedActiveHit.lean` composes the generic active-prefix bounded-hit extraction with both gated literal-halt witness reductions. For arbitrary finite PR run and hit codes, a seed, and each candidate PRA model satisfying IΣ₁, `haltToCodeHit` reduces a literal halt witness to a bounded nonzero hit-code witness, assuming gated synchronization, persistence of physical halting, and nonhalting of good frames. `codeHitToHalt` reduces a nonzero hit-code witness to an explicit literal halt witness, assuming the same synchronization and an all-good-hit physical halt-segment contract. The two bounded-hit-supplier assumptions in the earlier gated framework are discharged by the PR active flag and its model-length induction.

These are Lean model theorems, not object-iPRA proofs; they do not discharge the physical contracts, show that any particular codes implement the pinned machine, or prove a machine consistency implication. The repository's `PA194SchedulerIteration.haltAt` is a concrete PR halt-test code for an abstract proof-enumerator scheduler. Its connection to a halt site of the 3,673-instruction physical source controller and to the displayed physical contracts remains open. It must not be silently identified with a controller source hit.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-gated-active-hit.sh "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The wrapper checks source hashes and named retained-object hashes, rejects inherited Git overrides, and builds seven modules in a fresh common output, checking printed axiom reports and the absence of `sorryAx`. The machine-specific baseline, graph overlay, and project and package foundations are prebuilt. The graph overlay's complete transitive closure has not been rebuilt coherently with all other retained roots; named hashes and the baseline manifest identify artifacts but do not establish their full provenance. This is a staged replay, not a self-contained source build.
