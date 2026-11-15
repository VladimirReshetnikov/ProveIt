# Lean endpoint specification

`PuiseuxTarget.lean` is an **uncompiled interface**, written against ProveIt
commit `d851229c33ef395db8dc04baf28c6a291073f61e`, Lean 4.32.0. It does not
prove Puiseux's theorem. No Lean compiler was available in this run.

The file specifies the numerical program interface, explicit closed
object-language formulas for finite factorization jets and rational tail
bounds, and the required deeply embedded derivation type. It also contains
small structural QF checks and transport of a supplied object derivation to
the concise native calculus. These source proofs remain uncompiled.

All `Programs` fields are obligations to implement and verify. No arbitrary
program tuple is asserted to meet the intended semantics. In particular,
the final theorem is conditional on an existing `InternalPuiseux` derivation;
it is not such a derivation.

To begin checking in a clean pinned ProveIt checkout:

```sh
lake build ConciseIPRA
lake env lean /absolute/path/to/PuiseuxTarget.lean
```

Complete the primitive-recursive implementations and their object-theory
proofs before claiming `InternalPuiseux concretePrograms`. Inspect the final
type and run `#print axioms` on that declaration, then rebuild its declared
dependency closure from source.

There are no `sorry` terms or postulated Puiseux axioms in this interface.
