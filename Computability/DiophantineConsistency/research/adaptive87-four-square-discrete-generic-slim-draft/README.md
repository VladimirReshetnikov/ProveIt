# Import-only generic proof alternative for 88/30

This inert source snapshot changes exactly one import from the `FourUnitGeneric` alternative in `research/adaptive87-four-square-local-mod4-model-draft/`: `ModelCarrierScaled` is replaced by `DiscreteOrderedRingFacts`. The generic proof uses that namespace's `Discrete` and `eq_one_or_neg_one_of_mul_eq_one`, both declared in the pinned direct source. Its other explicit imports provide `ZMod 4`, `linear_combination` and `nlinarith`. The source, original theorem bodies, locally copied mod-4 facts, and public theorem signatures are otherwise byte-for-byte unchanged. This is a source-level dependency observation, **not** a claim that Lean elaborates the draft.

Using the pinned predecessor's current-source import graph, the checker recalculates both closures:

| Closure | Before | After | FactorUnits remains reachable? |
| --- | ---: | ---: | --- |
| Conditional model client | 458 | 451 | No, in this lexical scan |
| Client plus `HAAdaptiveFactor87.polynomialBridge` | 658 | 651 | Yes |

Both lose exactly seven source names: `ModelCarrierScaled`, `Carrier65`, `ConsecutivePell`, `ShortCircuit`, `ShortEquation`, `ShortSystem`, and `TotalDegreeBound`, all in `DiophantineConsistency`. These are source-declared initial-import reachability results, not claims about dynamic imports or objects. The parent bridge is still an explicit premise in the conditional client; instantiating it restores the separate FactorUnits ancestry described by the predecessor packet.

For the 651-name instantiated closure, the sample peer overlay currently has 651 resolving `.olean` paths, while the two additional roots have 293 and 561 respectively. Presence is not compatibility or object authentication. The peer overlay is a mix of historical providers as documented in `research/adaptive87-four-square-peer-provider-inventory/`; its package roots, source ancestry, object consistency and companions remain open. No build readiness or iPRA theorem is claimed.

Run from the DiophantineConsistency directory:

```sh
python3 research/adaptive87-four-square-discrete-generic-slim-draft/check.py > /tmp/adaptive87-discrete-generic-current.json
cmp research/adaptive87-four-square-discrete-generic-slim-draft/result.json /tmp/adaptive87-discrete-generic-current.json
```

The checker verifies the exact one-import edit, the two underlying declarations, hashes all sources in the predecessor combined graph, and recomputes the conditional and instantiated frontiers. It does not run Lean, stage files, copy or change providers, or authenticate compiled objects. The retained `/tmp` provider observations can change.
