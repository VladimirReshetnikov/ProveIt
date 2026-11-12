# Source-only composition from auxiliary norms to strict bounds

`NormsToBounds.lean` is an **unelaborated and uncompiled source proposal**. It attempts to compose three independently source-reviewed, also uncompiled fact-level drafts: `../ordinary14-model-main-square-gap-draft/MainSquareGap.lean`, `../ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean`, and `../ordinary14-aux-geometry-model-draft/AuxGeometry.lean`. Bare import names describe a possible future overlay, not an authenticated source/object/provider route. No literal graph theorem, Lean/iPRA endpoint, PDF/JSON/gzip binding or prior provider replay is claimed.

The proposed `aux_bounds_of_natural_norms` assumes positive natural X, Y, eta, zeta and i; the exact c and Delta identities; natural first and main Pell square equations; the natural strong equation `(i*c²)²+Delta=Delta*f²`; and explicit signed difference-ring bindings `Q=(ι i*ι c²)²`, `z+ι c=(ι f)²*t`. The strong equation is written without truncated subtraction. Under exactly those premises the source composes the proposed k=2 exclusion, k≥8XY²+4 descent and positive-parameter geometry, casts c and Delta bounds and the strong equation into `DiffRing V`, then applies the proposed strong and signed-gap facts to obtain **`1<Q ∧ 1<z²`**. This matches the strict assumptions of `../ordinary14-aux-root-model-draft/AuxRootBridge.lean`, but this composition does not itself import that lemma or construct an auxiliary-coordinate witness.

The individual source lemmas, this composition, all local casts and rewriting/typeclass/tactic behavior remain untested by Lean. The source checker verifies statement/premise inventory and reruns component finite-control receipts; it is not a proof of the model statement, the imports, or elaboration. A future compiler run needs independent prelaunch review, a coherent exact source/object/Init overlay and transitive provider route, the established disk/resource guard and exclusive allocation.

The **remaining graph-specific gap** is to extract from an actual 78/79 positive graph zero the natural first and main roots, c and Delta identities, and natural strong norm; prove the signed definitions of Q and z in the difference ring, including the conditional natural subtraction/cast issues; and connect these bounds and the existing conditional auxiliary witness lemma to literal graph evaluation and positive slot updates. Compact44 port identification, the 84↔85 and other parent model clients, iPRA endpoint and any external file semantics remain separate.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-aux-norms-to-bounds-draft/check_source.py > /tmp/aux-norms-source.json
cmp /tmp/aux-norms-source.json research/ordinary14-aux-norms-to-bounds-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-aux-norms-to-bounds-draft-independent/`.
