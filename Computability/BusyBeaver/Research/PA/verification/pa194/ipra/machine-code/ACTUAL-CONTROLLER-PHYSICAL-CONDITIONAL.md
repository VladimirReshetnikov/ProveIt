# Conditional physical/controller halt equivalence

`PA194ActualControllerPhysicalConditional.literalHaltIffControllerHalt` specializes the existing gated site-10 physical-halt framework to the actual encoded source-controller run and PC. In a PRA and IΣ₁ model, from any working initial controller PC, the literal physical machine starting at `start` eventually halts if and only if the encoded controller eventually reaches sentinel 3,674.

This conclusion is conditional on two explicit, unproved hypotheses. The first supplies a model-uniform synchronization of active controller states with state-24 physical frames, including elapsed-time domination; the second says that controller site 10 has the required concrete physical path-10 tape representation. The theorem does not construct those functions, prove either hypothesis for PA194, identify the separate scheduler run with the controller, or provide a native iPRA consistency proof. The functions and `good` predicate in the hypothesis are arbitrary model functions; no definability claim about them is made.

The new source is `PA194ActualControllerPhysicalConditional.lean`. The fresh-output checker rebuilds it after the actual-controller halt-reachability sources and the separate site-10 physical-halt framework. Invoke from the repository root with:

```
/dev/shm/pa194-source-haltbridge/check-actual-controller-physical-conditional.sh "$PWD" /dev/shm/pa194-model-length /dev/shm/pa194-source-controller /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-source-haltbridge /dev/shm/pa194-halt-path
```

The checker regenerates the pinned source tree, rebuilds the controller and site-10 theorem chains together, checks the literal table hash, and audits theorem axiom reports. The coherent machine baseline, graph overlay, and foundational overlays remain prebuilt; direct hashes do not authenticate their complete transitive closure, and source/tree/table pinning does not prove physical synchronization. The independent replay log is `/tmp/pa194-actual-controller-physical-conditional-replay.log`; consult final PASS and exit status before relying on it.

The repository-source replay also passed using this directory for all four
source-directory arguments with the same retained overlays.
