# Lean blueprint

`IPRAAbelRuffiniBlueprint.lean` records the intended imports, namespaces,
certificate interfaces, and final theorem shapes. It contains no `axiom` and
no `sorry`, but its `opaque` declarations are implementation boundaries, not
completed definitions.

To use it in ProveIt at the pinned revision:

1. Place the file under a new application directory visible to both the
   `Algebra/PolynomialFormulas/Lean` and
   `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean` Lake packages, or
   create a small umbrella Lake package with those two source directories.
2. Replace each `opaque` declaration by the primitive-recursive definitions
   described in Chapter 11 of the report.
3. Add the target theorems in dependency order.
4. Add `#print axioms` checks for the public iPRA and native endpoints.

The existing semantic modules are already useful regression oracles, but the
object-theory proof must establish the coded checker equations inside
`PRAAx`; importing a semantic theorem alone does not perform that step.
