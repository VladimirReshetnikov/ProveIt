# Internal substitution matrix inversion

`matrix_witness` recovers the original formula structure under simultaneous
substitution. In an arbitrary candidate-PRA model whose arithmetic reduct
satisfies IΣ₁, suppose that a well-formed source formula is fixed by bound
shift and that substituting a valid term vector into it produces
`x ∨ (y ∨ ∀ k)`. The theorem exhibits original disjuncts and a universal
body, proves their well-formedness and the body's shift fixedness, and gives
the exact equation `subst L (qVec L w) q = k`. All codes and vector lengths
may be nonstandard.

This composes the generic ∨/∀ inversion results with the matrix argument used
by the upstream PA196 induction-axiom supplier. It is generic over the encoded
language and the valid substitution vector; it does not yet instantiate the
unported PAeq translation or produce an induction-axiom proof code.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-subst-matrix/check.sh
```

The final module passed a fresh suffix check using the newly checked
substitution inversions and retained prerequisite overlays. Its printed axioms
contain no `sorryAx`. The full nested replay remains pending.

An independent suffix replay rebuilt the matrix module against separately
checked forward-node and scheduler prerequisites, with retained deeper
overlays. It passed without `sorryAx`; this was not a full nested replay.
