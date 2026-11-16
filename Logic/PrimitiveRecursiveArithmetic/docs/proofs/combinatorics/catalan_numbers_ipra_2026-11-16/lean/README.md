# Lean artifacts

- `CatalanExecutable.lean` is a self-contained executable specification using
  `Std`: Pascal binomial coefficients, the division-free Catalan definition,
  a small Dyck-word checker, and decidable examples.
- `CatalanProveItBlueprint.lean` imports the exact checked ProveIt Catalan
  theorem and defines the first object-language terms for the extension.

Neither new file contains `sorry` or introduces axioms. The build environment
for this delivery did not include `lean` or `lake`, so they are not claimed to
have been compiled. The imported ProveIt theorem is independently kernel
checked in repository snapshot
`00bbe871268c453903499fb6afe07519e87d9631`.
