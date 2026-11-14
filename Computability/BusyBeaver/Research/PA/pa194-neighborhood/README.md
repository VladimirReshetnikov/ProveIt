# PA194 neighborhood equality interfaces

`PA194Logic.primitiveToNeighborhood` constructs a finite PA194-calculus
derivation of primitive equality implying the defined two-sided membership
neighborhood relation at any binder distinct from both equality labels.
`PA194Logic.neighborhoodWitness` derives the corresponding existential
witness. The proof first uses the equality-code binder and the separate
self-diagonal head, then transports to an arbitrary permitted binder using
membership vacuity and the retained witness; it handles equality with the
special binder separately. Both theorem axiom lists are `[propext,
Classical.choice, Quot.sound]`.

These are finite standard-Lean derivations in the displayed PA194 numerical
calculus. They do not by themselves translate PA refutations or prove an
internal PRA/iPRA statement. The source-tree generation boundary is documented
in `../pa194-source-tree/README.md`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-neighborhood/check.sh
```

The script rebuilds the reverse-rewrite prerequisites in private tmpfs, then
checks the neighborhood proofs. The Lean modules have passed an independently
built overlay check; the full standalone script has not yet completed.
