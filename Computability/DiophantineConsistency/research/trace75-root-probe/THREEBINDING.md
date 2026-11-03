# Main index three forces first index two

`Trace75ThreeBinding.first_index_eq_two_of_main_three` is checked in every
`IΣ₁` model. For arbitrary natural ports with beta positive, positive trace75
witnesses and a zero of the Lean trace75 ring value, any `n` satisfying the
unscaled first-ordinate equation

```
2*ycoord n (2*(X*Y²-1)+1) = k
```

must equal 2 if additionally `c = ycoord 3 (A-1)`, where the local
`A=X*Y+Y`. The proof obtains X,Y≥2 from the actual positive graph inputs,
uses the generic n≥3 contradiction, and invokes the existing graph-specific
n≥2 theorem. The main-index-three premise is explicit. This does not exclude
it, since n=2 remains possible at this stage, and does not establish r≥5,
halting, an iPRA theorem or Lean binding of external JSON/payload files.

Accepted source `Trace75ThreeBinding.lean` SHA-256
`ac4412515cda1f7418fec8ebf1c5ef27028dd8a9cc941de4a2cc9d2e25f8f1e9`;
`run-threebinding.py` accepted `observations/threebinding-attempt01/`, object
`/tmp/trace75-threebinding-htxax7h3/Trace75ThreeBinding.olean` SHA-256
`a66ff3021153cafb70db06a89dd9ca83be49aa162c008ef9cb7e50d84da43877`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
Selected direct providers are pinned; project/package transitive, historical
source/object and dynamic ancestry remain inherited.
