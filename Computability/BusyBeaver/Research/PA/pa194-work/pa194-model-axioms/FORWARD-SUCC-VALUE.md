# Universal source theorem for a successor-variable value

These four modules take the checked natural-deduction normalization of the actual forward translation of `succ (.bvar 0)`, package its two directions as one source equivalence, and discharge its four equality assumptions using proofs in the full adjunctive-plus-separation source theory. They close its two standard free variables, prove the exact typed two-binder template correspondence, and obtain `successorValueUniversalProof` in every candidate-PRA model whose arithmetic reduct satisfies IΣ₁.

The theorem says that the translated relational value of the successor of a variable x at z is equivalent to `domain(x) ∧ domain(z) ∧ successor(x,z)`. Its `successorValueClosedGraph` defines the closed **formula code**, not a proof code. The open and universal proof codes are supplied by Lean constructions whose uniform Σ₁ proof-code graphs are not established here.

This is a fixed standard-syntax source theorem. It does not prove substitution into arbitrary internal formulas, invariance under isomorphism, the translated PA induction axiom, native iPRA internalization, or machine correctness.

Run `bash check-forward-succ-value.sh REPO NEW_OUTPUT`. It rebuilds all four new modules in a single fresh output against pinned prebuilt inputs, including the exact repository-replayed successor-variable normalization and unified translator. The full transitive source closure is not rebuilt. Success includes ten axiom reports with no `sorryAx`.
