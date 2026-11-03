# Trace75 joined Pell witnesses with their actual V square

`Trace75JoinedSquare.strong_and_auxiliary_indices_with_graph_residue` is a
strengthening of `Trace75Joined` for arbitrary natural ports with beta
positive and a positive trace75 zero in any `IΣ₁` model. It exports the
same tuple `tau,f0,V0,y,I,j,h` with the previous first roots, strong index,
odd auxiliary index and signed residues, **and** the equation

```
V_register * V_register = ι(V0*V0)
```

for that very same V0. This is needed for the signed rank argument; it avoids
identifying witnesses from separate existential theorems. The witness h is
natural, not claimed positive here, and Z0 remains internal. The result is a
necessary graph-zero consequence, not rank/index equality, halt/iPRA,
trace74 reverse guard or a formal JSON/payload binding.

Accepted source `Trace75JoinedSquare.lean` SHA-256
`39c3780be09f7e533a44ff5a59123c5b3d67d70141a1ba49e07cbdd59196f86c`;
`run-joinedsquare.py` accepted `observations/joinedsquare-attempt01/`, object
`/tmp/trace75-joinedsquare-qur93i_u/Trace75JoinedSquare.olean` SHA-256
`09ab5f30401baa3f93c69db97a44b4c6f5c3fc0dbdd7b08770ba623af925d620`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`. Selected
direct providers are pinned; project/package transitive, historical
source/object and dynamic ancestry remain inherited.
