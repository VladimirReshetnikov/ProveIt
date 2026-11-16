# The successor dispatcher and typed value template agree

`PA194SuccVariableTemplate.lean` proves that, for arbitrary model-valued free-variable indices x and z, the actual numerical term dispatcher applied to the primitive PAeq successor-variable term and the explicit bound/result packet returns exactly the code of the typed forward-value template specialized at x,z. The proof gives an exact standard-template expansion, then checks quotation and substitution through the existential binder with model-valued indices; it does not infer the model-level result merely from standard instances.

`numericalDispatcher_eq_template` holds in every arithmetic IΣ₁ model. Combined with the separately checked arbitrary-index source theorem, this aligns that theorem's translated-value side with the numerical dispatcher's output. It does not yet provide arbitrary-term value totality, atomic Leibniz, general formula substitution, the PA induction bridge, a native iPRA theorem, or machine correctness.

Run `bash check-succ-variable-template.sh REPO NEW_OUTPUT`. The new source is rebuilt in a fresh output against pinned prebuilt inputs, including the exact repository successor dispatcher and arbitrary-index value theorem. The full transitive source closure is not rebuilt. A successful run contains three axiom reports without `sorryAx`.
