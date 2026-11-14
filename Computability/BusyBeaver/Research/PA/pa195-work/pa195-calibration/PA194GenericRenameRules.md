# Internal free-label renaming and formula constructors

`PA194GenericRenameRules.lean` proves that the parameterized internal
free-label traversal of `PA194GenericRenameBase` preserves term and formula
well-formedness at every model-valued bound depth. It provides constructor
equations for atoms, truth constants, conjunction, disjunction, and both
quantifiers, and proves that renaming commutes with Foundation's internal
syntactic negation. These results apply to arbitrary, including nonstandard,
well-formed internal syntax and map parameters.

They hold in every nonempty candidate-PRA model with equality and an IΣ₁
arithmetic reduct, for any supplied Σ₁ graph correct for the selected
parameterized map at every model value. No semantic truth predicate or
injectivity assumption is used. Lean reports `propext`, `Classical.choice`,
and `Quot.sound` for the printed theorem dependencies, without `sorryAx`.

Together with the preceding internal PA-axiom invariance, these identities
support the axiom, cut, and propositional branches of a prospective derivation
renamer. They do not establish those proof transformations: substitution,
eigenvariable and shifted-context compatibility, encoding formula contexts,
and recursion over internal derivations remain open. They do not prove an
iPRA theorem or either PA194 consistency implication.

Run `check-generic-rename-rules.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set; it rebuilds the dependencies in a fresh
temporary overlay and rejects `sorryAx`.

An independent fresh `check-rename-shift-compatibility.sh` replay also rebuilt
this module and its local prerequisites using the audited overlays, with no
`sorryAx` in the checked theorem dependencies.
