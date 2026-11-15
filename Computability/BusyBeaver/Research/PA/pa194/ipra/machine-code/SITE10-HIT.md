# Primitive-recursive site-10 hit and physical halt

`PA194Site10Hit.atSite10` constructs a finite primitive-recursive characteristic code for an arbitrary encoded program-counter function equaling model numeral 10. `atSite10Model` proves the characteristic's exact meaning in every candidate PRA model. In models whose arithmetic reduct satisfies IΣ₁, `site10ReachesLiteralHalt` combines this hit code with generic active-prefix first-hit extraction and the exact three-step literal site-10 path segment.

The theorem requires the displayed gated synchronization and clock bound, plus a representation property that states whose encoded PC is 10 have a packed root frame containing actual source path 10 followed by an arbitrary model-valued suffix. Its run and PC codes remain parameters. It does not construct the source-controller state encoding or prove that its run is synchronized to the machine; it does not equate scheduler halting with site 10. The proof is a model theorem, not a native iPRA consistency implication.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site10-hit.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The staged checker recompiles eleven source modules in one fresh directory, pins selected source and object hashes, rejects inherited Git overrides, and audits printed theorem axioms. It retains the prebuilt machine baseline, graph/equality-code overlay, and general project and package foundations; their full transitive provenance and cross-overlay compatibility have not been independently reconstructed here. It is not a self-contained source build.
