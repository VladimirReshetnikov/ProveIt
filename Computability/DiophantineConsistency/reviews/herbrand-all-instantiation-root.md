# Candidate PRA witnessing for open ∀∃ formulas

`PRA_witness_of_exists` proves in Lean that, for any Foundation open matrix
φ with one witness variable and finitely many parameters, a candidate-PRA
proof of its universally closed existential sentence yields a fixed
primitive-recursive code of exactly the parameter arity and a candidate-PRA
proof of the matrix instantiated with that code. The proof translates the
candidate theorem to the explicit universal presentation, specializes its
universal quantifiers while retaining the finite axiom list, eliminates cuts,
extracts finitely many terms, translates them to parameterized codes, and
selects one witness. The derivation existence construction uses Lean's
classical metatheory and completeness.

This is a witnessing theorem for the repository's **candidate** PRA theory,
not identification with a standard PRA presentation and not IΣ₁-to-PRA
conservation. It does not by itself yield a PRA proof of the Diophantine
equivalence, whose IΣ₁ proof is the required input to the missing conservation
step.

After upstream changed eleven prerequisites, two isolated builds rebuilt 43
affected source-current local modules plus the new theorem and checks. All
45 source, object and complete-log hashes match. The driver verifies ten
unchanged inherited local source/object pairs and rebuilds the rest of the
53-module local target graph. [Independent driver, state and logs](herbrand-all-instantiation-root-replay/)
and the [author packet](herbrand-all-instantiation-author-replay/) are
preserved. The five final axiom reports list `propext`, `Classical.choice`,
and `Quot.sound`. Foundation/Mathlib and the ten unchanged local objects
remain inherited cache boundaries, not a fresh transitive source audit.
