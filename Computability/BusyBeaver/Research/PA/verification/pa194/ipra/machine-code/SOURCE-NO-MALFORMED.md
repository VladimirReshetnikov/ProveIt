# Source-controller model-time invariant conditional on complete resolution

`PA194SourceNoMalformed.AllResolved` states that each of the 3,673 actual pinned source ordinals has a successfully resolved instruction. Assuming this *external finite-table premise*, `stepWorkingOrHalt` proves that an encoded source state with model-valued PC <3673 steps either to another working PC <3673 or to halted sentinel 3674. It uses the proved destination range theorem, so normal root exit is included. `stepValidPC` includes halted-sentinel stuttering, and `runValidPC` uses model IΣ₁ induction and PR graph definability to extend this disjunction to every model time, including nonstandard times, from a seed satisfying the same disjunction.

`AllResolved` is not discharged by this module. The existing separately checked 3,673-site coverage certificate implies it, but the retained coverage aggregate was not imported or coherently replayed here. The result is a Lean model theorem, not an object-iPRA statement. It does not prove source/physical synchronization, scheduler correspondence, or a Con(PA) direction.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-source-no-malformed.sh "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The staged checker pins named source and object hashes, rejects inherited Git overrides, recompiles twenty source modules in a common fresh output, and checks theorem axioms. The machine/source-tree baseline, graph/equality overlay, and project/package foundations remain prebuilt; their complete transitive provenance and cross-overlay compatibility have not been independently reconstructed here.
