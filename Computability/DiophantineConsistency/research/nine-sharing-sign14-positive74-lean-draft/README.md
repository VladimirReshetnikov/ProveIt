# Positive74 symbolic syntax and formal transport plan

`generate.py` derives ten source-only Lean modules from the independently reviewed positive74 residual AST. Nine ordered modules name the 65 live residual DAG operations; the last names the five rows and their sum of squares. External JSON variables 1–14 map to `Fin 14` indices 0–13, and ports beta/K0/MC/MF map to indices 0/1/2/3. The output is a proposed actual positive-input expression, not a theorem connecting the JSON or PDF to Lean. No generated module has been compiled.

The intended core ring identity, for arbitrary commutative ring `R`, ports `p` and `v : Fin 14 → R`, is

```lean
(Sign14Positive74.expression p).evalRing (fun i => v i + 1) =
  (Sign14Optimized86Expression.expression p).evalRing v
```

Prove it via small named-node/row evaluation lemmas, using `Sign32GenericRemoveInput.eval_removeInput` to connect the old 15-coordinate seed and its `Fin.cons 1 v` environment. Prove additions/subtractions/multiplications and numeral casts using explicit evaluation lemmas and ring normalization, in bounded stages; avoid unfolding the entire seed in one elaboration. Every row must be covered and the final sum association verified.

Then `internalZero_positiveShift` and the ring identity should yield pointwise, and hence existential, model-zero equivalence between `positiveShift (Sign14Positive74.expression p)` and the checked natural-coordinate 86 expression, in every relevant arithmetic model. The all-model transport supplies the existing polynomial bridge and native/standard/translated iPRA endpoints for the positive-domain formula. Exact degree 124 is a separate affine-translation theorem or coefficient proof; do not infer a Lean result from the external ring observation. The positive statement ranges over 14 strictly positive elements; `positiveShift` represents this with natural witnesses. Formal syntax-to-external-AST/JSON and PDF semantics remain separate obligations.

The syntax stages and proposed statements must receive independent source review and a fresh bounded Lean guard before any result is claimed. The external gate count describes this positive-input DAG under the documented sharing convention and is not the count of `positiveShift` as a natural-input circuit.

Independent structural audit passed: `../../reviews/nine-sharing-sign14-positive74-lean-draft-independent/`. No Lean result is claimed.
