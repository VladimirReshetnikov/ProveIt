# Source-only 78↔79 auxiliary-coordinate graph client

`AuxGraphEquivalence.lean` is an **unelaborated and uncompiled source proposal** for the all-positive valuation existence comparison between the reviewed literal 79 and 78 graphs. Its bare imports `GraphNormClient` and `AuxRootBridge` refer to separately source-reviewed but uncompiled drafts and a proposed future overlay, not authenticated object/provider routes. No Lean theorem, iPRA endpoint, degree claim or external PDF/JSON/gzip binding is established.

The proposed client changes **only slot 11**: the old graph uses positive u and computes `y=z+u`; the new graph uses positive y directly. It proposes `putAux_self` and positive-update lemmas, definitional equality and slot-11 independence of the other four fields, and the exact signed auxiliary/output evaluations. `old_aux_eval` and `new_aux_eval` target the existing conditional `oldAux`/`directAux` ring expressions; no natural subtraction is substituted for the signed z value.

In the 79→78 direction, the proposed theorem obtains `1<Q` and `1<z²` from the **starting 79 graph zero**, then applies the independently drafted conditional auxiliary witness lemma to produce positive y. In the other direction it obtains the same bounds from the **starting 78 graph zero**, then obtains positive u. It does not presume an old witness or graph zero in the reverse direction. The four non-auxiliary fields are held fixed and the direct `DiffRing V` output identities are used to return `InternalZero`; all fourteen coordinates are shown positive using the slot update. The statement assumes a positive natural beta and explicit `(p 0 : DiffRing V)=ι beta`; `positive_zero_iff_natural_ports` proposes a natural-port specialization via `P72Root.cast_port`. Neither statement identifies external byte payloads or proves the parent endpoint.

These are source scripts only: all graph definitional equalities, `simp`/`ring` field evaluations, positivity, natural-cone extraction, casts, `InternalZero` rewriting, imports and resource behavior are untested by Lean. They depend on the uncompiled `../ordinary14-aux-graph-norm-client-draft/` and `../ordinary14-aux-root-model-draft/` and their own source/provider chains. The checker pins the sources, independently compares the four other graph fields as slot-normalized expression trees, replays component source receipts, and tests both signed coordinate substitutions on 200 finite integer assignments. Those controls do not prove the unbounded or arbitrary-model statements.

Before any future Lean run, independently review this source and exact direct/transitive source/object/Init provider routes, assemble a coherent overlay, check the established disk/resource guard and obtain exclusive allocation. Even a successful local theorem leaves 84↔85 and other parent model bridges, compact44 port binding, iPRA endpoint and any external file semantics separately open.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-aux-graph-equivalence-draft/check_source.py > /tmp/aux-graph-equivalence-source.json
cmp /tmp/aux-graph-equivalence-source.json research/ordinary14-aux-graph-equivalence-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-aux-graph-equivalence-draft-independent/`.
