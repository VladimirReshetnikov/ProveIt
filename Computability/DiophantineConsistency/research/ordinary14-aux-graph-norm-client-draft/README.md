# Source-only 78/79 graph-to-auxiliary-bound client

`GraphNormClient.lean` is an **unelaborated, uncompiled source proposal**. It attempts to extract the auxiliary inequalities `1<Q` and `1<z²` from either literal 78 or 79 positive graph zero by composing the source-only factor-level ring/natural norm route. It does not yet prove the 78↔79 coordinate map, a global existence equivalence, iPRA endpoint, degree theorem, provider ancestry or PDF/JSON/gzip binding.

The bare imports `P79DirectPell`, `P78AuxRoot`, `FirstRootBridge` and `RingNormExtraction` are proposed future overlay names for separate, uncompiled draft sources. Their direct/transitive source/object/Init providers have not been authenticated or tested together. The 78 literal graph is itself a fresh source draft in `../ordinary14-aux-root78-lean-draft/` and still needs independent review. The ring-norm extraction draft is separately awaiting source review.

## Proposed model statements

For `ORingStructure V` modeling IΣ₁, the client defines natural q, X, Y, U, k, a, c and Delta from a natural beta and the literal positive valuation. The rank and main carrier remain **difference-ring expressions**, so no sign or natural representation of rank or the main carrier is assumed. All theorems requiring the integer port specify the explicit cast equality `(p 0 : DiffRing V)=ι beta`; `p 1`, `p 2` and `p 3` remain arbitrary integer leaves.

The proposed `first_eval`, `main_eval` and `strong_eval` identify the 79 graph's three fields with the explicit ring equations required by `RingNormExtraction`. `fields_of_zero` proposes five-square zero extraction. `common_norm_fields` proposes definitional equality of the first, main and strong field expressions of the two graphs; `fields_of_78_zero` uses the 78 graph's **own** output zero and does not assume a 79 zero. `bounds_of_fields` composes the explicit field identities, positive X/Y/U and positive eta/zeta/i with the separately drafted sign-free natural norm extraction and factor-level bounds. `bounds_of_79_positive_zero` and `bounds_of_78_positive_zero` are proposed wrappers for their respective graph zeros. The latter does not identify the two auxiliary fields or reuse an old u witness.

The source proofs, `rfl` on graph fields, `simp`/`ring` evaluation, sum-of-squares rewriting, casts, typeclass inference and resource behavior have not been checked by Lean. `check_source.py` independently parses both literal JSON graphs, compares exact first/main/strong expression trees with input slots normalized, verifies the displayed signed rank/carrier/Q/z formulas and output square sums on 100 finite integer controls, and pins all draft source hashes. This is **not** a universal model proof, elaboration check, or preflight.

After independent source review and eventual guarded compilation, the remaining local step is to prove the actual 78↔79 auxiliary field substitution, positive slot-11 updates and equivalence of outputs using the conditional witness lemma. The 84↔85 modified-carrier model proof, other parent bridges, compact44 provider/port binding and iPRA endpoint remain separate. Any future Lean run requires a reviewed coherent source/object/Init overlay and transitive provider route, the established disk/resource guard, and exclusive allocation.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-aux-graph-norm-client-draft/check_source.py > /tmp/aux-graph-norm-source.json
cmp /tmp/aux-graph-norm-source.json research/ordinary14-aux-graph-norm-client-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-aux-graph-norm-client-draft-independent/`.
