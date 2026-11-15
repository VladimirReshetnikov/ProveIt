# A matched controller/physical frame relation for site 25

`PA194Site25FrameRelation.Matched site gap source physical` relates the finite PR source-controller encoding to a literal physical root frame at a specified source site and zero-run count. It existentially chooses eleven physical/logical values and an independent controller-file tail. The gap is an explicit parameter: physical transitions may change it while the source-controller register-file tail is preserved.

`site25Step` proves in every candidate PRA model that a related site-25 pair whose gap is `(k+1)+1` takes one encoded controller step and some literal physical number of steps to a related pair, either at site 27 with gap `k+1`, or at site 26 with gap `((k+1)+1)+1`. It covers both register-8 branches uniformly and retains all physical spare/suffix information. The physical clock is existential in this statement, and the branch-specific physical theorems supply its explicit witness.

This relation is a Lean model-level predicate, with a witness of type `Fin 11 → M`. Its first-order/Σ₁ definability has not been established. Only site 25 is covered; this is not a model-length controller/physical simulation, scheduler calibration, native iPRA derivation, or Con(PA) implication.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site25-frame-relation.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site27-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The staged wrapper rebuilds the controller source chain, the zero-branch physical suffix, both source/physical branches and the relation in one fresh output. It validates selected source hashes and a receipt of direct physical baseline objects, and audits printed theorem axioms. The site27 machine baseline, graph/equality overlay, and general project/package foundations are retained prebuilt; their complete transitive provenance and cross-overlay compatibility are not reconstructed here.
