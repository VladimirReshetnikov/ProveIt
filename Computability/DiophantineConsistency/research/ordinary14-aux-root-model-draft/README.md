# Source-only model lemma for direct auxiliary coordinates

`AuxRootBridge.lean` is an **unelaborated and uncompiled source proposal**. It isolates the fixed-other-residual auxiliary witness map between the reviewed 79 and 78 graphs. It imports the separately source-reviewed but uncompiled `../ordinary14-direct-first-root-model-draft/FirstRootBridge.lean`; the bare import is a proposed future overlay name, not an authenticated provider route. No Lean, endpoint, iPRA, PDF/JSON/gzip binding or graph theorem is claimed.

In an arbitrary `ORingStructure V` modeling IΣ₁, z and Q are elements of `DiffRing V` and the old and new coordinates are positive natural model elements. The explicit assumptions are **`1<Q` and `1<z*z`**. From the direct auxiliary norm `y²−Q*(y²−z²)=1`, the proposed `square_gt_of_aux` derives `z²<y²`. The two order lemmas then show that old `y=z+ι u>z` is positive, and that a positive direct y satisfies `z<ι y`. `ModelDifferenceRing.nonneg_iff` and `ι_lt_ι` are used to represent each positive difference-ring value by a positive natural model element. `positive_aux_coordinate_iff` proposes the two existence implications while treating the other four residuals as fixed ring parameters and using the separately drafted five-square extraction.

These strict bounds are **assumptions of this fact-level result**, not silently assumed properties of all graph zeros. The 78/79 graph-specific client must derive them from its first/main/strong residuals: rule out k=2 using the main square, formalize the positive first-Pell descent needed for `k≥8m+4`, derive `Delta<c³`, use the strong norm to show `f²>c+1`, and use `f² | V+c` to exclude `V=−1,0,1`. It must also prove the literal signed expressions, independent slots, positive valuation maps and InternalZero evaluation bridges. None of these model-level results is supplied by the external standard-integer review alone. Nor is the 78 graph imported by this draft.

The proofs' `nlinarith`, order reasoning, natural-cone extraction, casts, theorem names and instances have not been tested in Lean. `check_source.py` checks the source inventory and finite integer norm controls, including a boundary showing why the z² assumption matters; it is neither a universal proof nor a Lean preflight. Any future compilation needs a coherent source/object/Init overlay, independently reviewed direct and transitive providers, the established disk/resource guard and exclusive Lean allocation. Even after a local compilation the graph-specific `z²`/Q bounds, 84↔85 and parent model clients, compact44 decoder and endpoint/iPRA routes would remain open.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-aux-root-model-draft/check_source.py > /tmp/aux-root-model-source.json
cmp /tmp/aux-root-model-source.json research/ordinary14-aux-root-model-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-aux-root-model-draft-independent/`.
