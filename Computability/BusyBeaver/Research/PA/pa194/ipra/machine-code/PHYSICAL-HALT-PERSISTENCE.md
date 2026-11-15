# PA194 literal halt persistence in models

`PA194PhysicalHaltPersistence.lean` proves that the totalized packed PA194 step fixes every configuration whose decoded control is at least 194 (`encodedHaltFixed`). It uses the pinned table's existing `ConfigurationStep.stepSem` totalization and packed encoding; all tape values may be arbitrary model elements. For every candidate PRA model whose arithmetic reduct satisfies IΣ₁, `haltedStepperFixed` lifts that fixed-point property to arbitrary, including nonstandard, model durations by Σ₁ induction. `haltPersists` then proves that once a packed literal run reaches a control at least 194, it remains there at every later model time. It can supply the persistence hypothesis in `PA194GatedActiveHit.haltToCodeHit` when halt is defined as control ≥194.

This is a Lean model theorem, not an object-iPRA derivation. It assumes the retained model/encoding and PR-code graph foundations. It does not prove source-frame nonhalting, physical synchronization, a halt instruction segment, or any scheduler/controller correspondence. The existing separate `PA194Reachable.haltIndicatorIffState` identifies the blank run's indicator with state 194; this handoff neither recompiles nor invokes that result.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-physical-halt-persistence.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The wrapper checks named source, baseline, and graph hashes and rejects inherited Git overrides. It recompiles eight sources in one fresh output and checks printed axioms for `sorryAx`. Its unified PA194 baseline, graph overlay, and general project and package foundations remain prebuilt. The graph overlay's complete transitive source closure and compatibility with the other retained roots were not reconstructed here; named hashes identify artifacts rather than authenticate all dependencies. This is a staged replay, not a self-contained source build.
