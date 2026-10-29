# Candidate PRA theory: independent replay

29 October 2026. I read the complete theory and checks, including the precise
arity and argument order of composition and recursion. The theory consists of
full equality, defining equations for the finite function codes, parameterized
open induction, successor nonzero/injectivity, and an explicit definition of
strict order. Lean verifies all these sentences in the defined natural-number
structure. The recursion step uses counter, previous value, then parameters;
the zero-arity cases are included in the universally quantified schemas.

An independent fresh Lean 4.32 replay with `-M6000 -j1 -DElab.async=false`
matched both author objects and complete logs. The main log is empty and six
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The [replay evidence](pra-theory-root-replay/) includes the independent driver,
state, logs and all 21 author source/log attempts and two check attempts.
Several intermediate author probes contain `sorry`; they are retained solely
as development history and are not part of the final source or accepted proof.
The replay used independently checked project parent objects and the reviewed
Foundation overlay with existing Mathlib cache, not a full transitive rebuild.

This is a candidate first-order presentation and standard-model validation.
The object-theoretic successor/add-one bridge, equivalence with a standard PRA
presentation, primitive-recursive axiom recognition, conservation, and the
requested PRA equivalence proof remain open.
