# Conditional physical-to-code-value-one reduction

For an arbitrary unary finite PR code `hit`, `PA194CodeOneHit.equalsOne` constructs a finite equality-characteristic code. `equalsOneModel` proves in every candidate PRA model (with the assumed IΣ₁ arithmetic reduct) that this code is nonzero exactly when `hit` evaluates to 1; no assumption that `hit` itself is Boolean is needed. `haltImpliesCodeOne` instantiates the checked control-24 root-frame conditional halt-to-hit result with that code. It reduces a physical literal halt witness to a bounded index where the original hit code has value 1, assuming the displayed gated synchronization and clock bound.

The equality-to-1 interface matches the premise of `PA194SchedulerIteration.initial_run_halt_provable`, but this module does not import or specialize to the scheduler, rebuild its closure, construct a physical/scheduler synchronization, or identify source-site 10 with a scheduler hit. All of these remain separate obligations; the theorem is a Lean model statement, not a native object-iPRA or consistency theorem.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-code-one-hit.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker verifies selected source and retained-object hashes, rejects inherited Git overrides, and recompiles ten modules in one fresh output with axiom audits. The retained machine baseline, code-graph/equality-code overlay, and general project and package foundation roots remain prebuilt. Their complete transitive provenance and cross-overlay compatibility have not been reconstructed by this replay, so it is a staged check rather than a self-contained build.
