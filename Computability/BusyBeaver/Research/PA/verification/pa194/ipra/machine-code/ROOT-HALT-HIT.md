# Physical halt implies a bounded hit, conditional on root synchronization

`PA194RootFrameNonhalt.lean` proves that every packed control-24 configuration is below the literal halt threshold 194, for arbitrary model-valued tape data. `haltImpliesCodeHit` then composes that fact with the proved PA194 physical halt persistence and the generic active-prefix bounded-hit extraction. In every candidate PRA model whose arithmetic reduct satisfies IΣ₁, for arbitrary finite PR run and hit codes, it derives a bounded nonzero code-hit witness from a literal halt witness, assuming gated synchronization with packed control-24 frames, good-state preservation as already embodied by that synchronization, and the clock bound shown in its statement.

The synchronization hypothesis is the remaining substantive premise of this conditional result: it has not been proved for all PA194 controller sites. The arbitrary hit code has not been identified with the controller's halting instruction or with `PA194SchedulerIteration.haltAt`; even when synchronization is later proved, a source-controller/scheduler calibration is still needed. This is a Lean model theorem, not a native object-iPRA proof or a machine consistency direction. The root frame theorem is valid for any tape value, but it does not construct the needed tape/frame encoding.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-root-halt-hit.sh "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker verifies named source and retained-object hashes, rejects inherited Git overrides, and compiles nine sources in one fresh output with axiom audits. Its machine baseline, graph overlay, and project and package foundations are prebuilt; the graph overlay's entire transitive closure and compatibility with all retained roots have not been rebuilt or authenticated. This is a staged replay, not a self-contained source build.
