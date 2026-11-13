# Pell carrier factor bound to the graph

`Trace74PellCarrierGraph.graph_carrier_factor` specializes the internal
Pell carrier factor to the actual `H ∣ K` premise of
`Trace74CRTNaturalTuple.exists_updated_carrier`. For one natural 74 tuple
it proves that premise from these explicit same-tuple bindings:

```
X = power 2 n,    c = ycoord n b,    X*Y+Y = b+1.
```

The index `n` is internal to an arbitrary IΣ₁ model, and `power` and
`ycoord` are the represented internal operations. This theorem does not
prove the three bindings for the concrete candidate; the six CRT Bézout
certificates and the remaining graph-zero conditions also remain open.

## Check

The following command exited 0 without warnings on 2026-11-04 with Lean
4.32.0 and previously built dependencies:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-pell-carrier-graph Computability/DiophantineConsistency/research/trace74-pell-carrier-graph/Trace74PellCarrierGraph.lean -o /tmp/Trace74PellCarrierGraph.olean
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
SHA-256 hashes for that run:

```
57d12f961f741ea02861d27e243428008b86f38746cda85824fef67b8be5c0ef  Trace74PellCarrierGraph.lean
27d54ff39df4259d29b464b3ba0a8476d3a687d774a8a41b6961a9ae507705f2  Trace74PellCarrierGraph.olean
debd4d64dfbd7a1403cee218fc125e71676a362095d3988416bd0077bcae0f44  Trace74PellCarrierInternal.olean
179954bfa22feb2c54af4d56f86e8276ca93b6a1f3d142aca56de0282dd1fda2  Trace74CRTNaturalTuple.olean
```

The `/tmp` paths are check-time artifacts, not persistent dependencies.
