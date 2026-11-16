# Numerical successor-variable dispatcher equation

`PA194SuccVariableDispatcher.lean` checks the actual numerical term dispatcher's result for the PAeq code `^func 1 1 [^#0]` (the primitive successor-variable term appearing in the induction body). For arbitrary model-valued indices x and z and the explicit packet with bound-variable value `&x` and result `&z`, its output is exactly `successorValue (&z) (variableValue #0 (&x))`. This is a model-level code equality; the singleton bound packet has a source domain variable and no free environment.

The module does not yet identify this expression with the typed template used by the universal successor-value theorem, nor prove arbitrary internal formula substitution, PA induction, an iPRA theorem, or machine correctness.

Run `bash check-succ-variable-dispatcher.sh REPO NEW_OUTPUT`. The source is compiled into a fresh output against pinned prebuilt inputs, including the repository numerical dispatcher equations. This does not rebuild the full transitive source closure. Success contains one axiom audit without `sorryAx`.
