# PA194 relational compiler interface

These modules adapt the PA196 relational interface and structural named-formula
encoding to the PA194 separate-diagonal derivation type. The interface uses
the PA194 reverse membership rewrites, arbitrary permitted neighborhood
binder, and neighborhood witness. It derives neighborhood vacuity, binder
change, universal specialization, and membership congruence. The encoding
module proves formula vacuity recursively for the translated named formulas;
the atoms module proves the membership and neighborhood-equality renaming
steps used by the compiler. The port also checks recursive substitution,
universal alpha-renaming, and canonical freshening.
The printed theorem dependencies are `[propext, Classical.choice, Quot.sound]`.

This is a checked connection to the relational compiler's interface, not a
completed PA-refutation translation. The upstream PA196 calculus also has an
equality-vacuity bundle that PA194 does not assume; this port uses the PA194
replacement interfaces instead. The downstream source LK compiler, the
primitive-recursive proof-code translation, and all PRA/iPRA internalization
remain open. The PA194 source-tree generation boundary is documented in
`../pa194-source-tree/README.md`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-relational-interface/check.sh
```

The script rebuilds the neighborhood prerequisites and pinned named-formula
modules in private tmpfs, then checks the interface and encoding. An
independent full standalone replay has passed.
