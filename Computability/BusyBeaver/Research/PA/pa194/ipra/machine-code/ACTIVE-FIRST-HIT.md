# Generic active-prefix bounded hit extraction

`PA194ActivePrefix.lean` defines a finite primitive-recursive active flag, initially 1, which retains its prior value on a zero hit test and becomes 0 on a nonzero test. `PA194ActiveFirstHit.lean` proves, in every candidate PRA model whose arithmetic reduct satisfies IΣ₁, the stronger invariant: either the flag at n is 1, or some i < n has flag 1 and nonzero hit test. Its proof uses Σ₁ induction, PR-code model graph definability, and the checked active recurrence. Arbitrary finite PR run/hit codes, seed, and possibly nonstandard n are permitted.

Consequently, `boundedHit` gives an active hit i ≤ n if the flag at n+1 is not 1, and `hitHasActivePredecessor` gives an active hit i ≤ n from a nonzero hit at n. These furnish the two separate bounded witness hypotheses of `PA194GatedModelLength.haltToSourceHit` and `sourceHitToHalt` when the gated active and hit predicates are respectively flag = 1 and the hit test ≠ 0. The extraction asserts existence, not a selected PR witness or a least-number theorem. It does not bind the run/hit codes to PA194, discharge physical simulation/halt hypotheses, establish a consistency direction, or constitute a native object-iPRA derivation.

Run from the repository root:

```
/dev/shm/pa194-model-length/check-active-first-hit.sh "$PWD" /dev/shm/pa194-model-length /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The wrapper hashes its five input sources and named baseline and graph dependencies, rejects inherited Git environment overrides, and recompiles the five modules in a fresh common output; it checks the listed axiom reports and absence of `sorryAx`. The retained machine-specific unified baseline, graph overlay, and general project and package foundation roots are prebuilt. In particular, the graph overlay supplies PR graph definability and other project objects; its complete transitive source build and compatibility with all other overlays have not been independently reconstructed here. The named object hashes and coherent-baseline manifest identify retained artifacts but do not authenticate their transitive provenance. This is a staged replay, not a self-contained full build.
