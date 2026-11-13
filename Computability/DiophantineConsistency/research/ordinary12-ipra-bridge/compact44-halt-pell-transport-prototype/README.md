# Model halt: one calibrated packing with Pell seeds and positive transport

`CompactHaltPellTransport.halt_pell_positive_transport` takes only the
model-internal decimal215 halt at time `T`, in an arbitrary `IΣ₁` model. It
constructs the same model-Σ₁-definable Boolean controller and pulsed word as
the sibling halt/Pell theorem, with the explicit controller support bounds,
the full symbolic compact `PackingInput`, the exact calibrated rank
congruence, and both complete Pell seed families. It additionally supplies
positive shifted transport for that *same* word, kernel, length and stride.

For `N=haltLength T`, `s=haltStride T`, the selected `X`,
`R=rank (paramKernel rho) N s X`, `q=Exp.exp (590069*N)`,
`w=Exp.exp (R-590069*N)`, `C=Cw 590069 N X` and
`F=Fw 590069 (paramKernel rho) N s X`, the new conclusion is

```
∃ z > 0, q*w = Exp.exp R ∧
  (paramKernel rho+w)*C = F+z*(q-1).
```

The same-word statement uses a local Σ₁ instance binder for the rank, seed
and transport expressions, and the preceding conjunct explicitly proves
that the constructed `X` has that instance. The proof applies the generic
calibrated-transport theorem to the packing and congruence returned by the
halt/Pell theorem. It derives `0<s` from the chosen power and `s<N` from
`CompactPackingGeometry.geometry`.

This is a symbolic all-model theorem. It does not yet construct all positive
coordinates, establish the exact free-J graph zero or its retained-byte/PDF
binding, or prove existence of a derivation in iPRA.

The single-author bounded run `observations/attempt01` actually exited 0
without warnings or `sorryAx`. Its named axiom report is exactly
`[propext, Classical.choice, Quot.sound]`, which records Lean metatheory
rather than added object-theory axioms. The source SHA-256 is
`45b7808fc81c0a70950fa720a9a1d98cdedc1dea6db289bc7308469ea455c8a7`; the
output object SHA-256 is
`26967b65400f5996de28976cd4bd405084f70cc809d9c8dce2ea725d41ca75c5`.
All 531 shared project names in the selected seed and halt overlays matched
at preflight. The direct import/companion guards, both selected project
inventories and other recorded roots were unchanged at the final checks.
The source, terminal receipt, dependencies, guards and overlap inventory
are retained under the attempt directory.

The point-in-time overlap and guard checks do not authenticate complete
transitive, package or dynamic ancestry. This is a mixed-provider exploratory
author build, not an independently reviewed paired replay; checks are not
continuous filesystem or whole-process-tree resource monitoring.
