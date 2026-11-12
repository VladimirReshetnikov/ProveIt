# Source-only positive-parameter auxiliary geometry

`AuxGeometry.lean` is an **unelaborated, uncompiled source proposal** for the Δ<c³ step in the 78/79 auxiliary-root model route. It assumes an arbitrary `ORingStructure V` modeling IΣ₁, positive natural Y and eta, the explicit large-k inequality `8*X*Y*Y+4≤k`, and the exact natural Delta identity `(X*Y+Y+2)²=Delta+1`. It does not extract any of these premises from a graph zero, establish a Lean theorem, or bind external bytes.

The proposed `geometry_of_large_k` gives `A<c`, `1<c`, `0<Delta` and `Delta<c³` for `A=X*Y+Y+2` and `c=eta+Y*k`. Its source proof factors the estimates instead of relying on a high-degree polynomial oracle: Y≥1 gives `X≤X*Y²`; the stated lower bound then gives `X+4≤k`. Thus `A<Y*(X+4)≤Y*k<eta+Y*k=c`. Since A≥2, c>1 and `A²=Delta+1`, one obtains `0<Delta<A²<c²≤c³`. All quantities and subtractions in this lemma are natural model terms; the Delta equation is explicit and does not treat ring subtraction as natural subtraction.

The uncompiled `../ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean` proposes the large-k inequality from an internal first Pell norm once k>2 is known. The separately uncompiled `../ordinary14-model-main-square-gap-draft/MainSquareGap.lean` proposes the k=2 contradiction from an exact natural main norm and Delta identity. A graph client must still extract and orient the relevant natural norms from the literal 78/79 residuals, bind k=eta+zeta and m=XY², establish the Delta identity, cast the resulting bounds into the difference ring, and invoke the conditional auxiliary-root witness map. No such graph client or global endpoint is claimed here.

The source tactics, rewriting, ordered-semiring instances, all imports and resource behavior remain untested in Lean. `check_source.py` performs source inventory and finite nonnegative integer controls, not a universal model proof or preflight. Any future Lean run requires independently reviewed coherent source/object/Init and transitive provider routes, the established disk/resource guard, and exclusive allocation. Compact44 decoder, parent and iPRA/PDF/file obligations remain separate.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-aux-geometry-model-draft/check_source.py > /tmp/aux-geometry-source.json
cmp /tmp/aux-geometry-source.json research/ordinary14-aux-geometry-model-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-aux-geometry-model-draft-independent/`.
