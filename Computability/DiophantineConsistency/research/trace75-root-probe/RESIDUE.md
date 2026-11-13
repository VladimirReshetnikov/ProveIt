# Signed trace75 residue

`Trace75Residue.graph_signed_residue` is checked in every `IΣ₁` model for
arbitrary natural ports and arbitrary valuations. Given any natural `u` whose
square represents the square of the signed trace75 V register in the model's
difference ring, it establishes

```
SignMod (1 + 2*Delta*U²*E) u c.
```

The theorem uses the actual unsquared trace register
`V = F*(c*T-rank)-c`, with `F=1+2*Delta*U²*E`. It does not assume a graph
zero, positive witnesses, fixed port bounds, or a trace74 coordinate guard.
It supplies signed modular information, not equality, Pell index alignment,
halting or iPRA equivalence.

Accepted source `Trace75Residue.lean` SHA-256
`44fb46d2a171d9abf066a6632695646e31195d4d02affb1fd04e8927d84f16b5`;
`run-residue.py` accepted `observations/residue-attempt01/`, object
`/tmp/trace75-residue-mpo1d0xl/Trace75Residue.olean` SHA-256
`205d69b70c084f2613a94f465f3b46fd59f142f755e34897dd4257b16c819e8d`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Selected direct providers and adjacent arithmetic dependencies are pinned; the
first applicable producer namespace overlay, package, historical transitive
source/object and dynamic dependencies remain inherited. No complete closure
audit or independent replay is claimed.
