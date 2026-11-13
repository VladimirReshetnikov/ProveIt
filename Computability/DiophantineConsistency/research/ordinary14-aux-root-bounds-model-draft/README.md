# Source-only model facts toward auxiliary-root bounds

`AuxRootBounds.lean` is an **unelaborated and uncompiled source draft**, not a graph theorem or a proof of the 78/79 model bridge. It isolates consequences needed to discharge the explicit `1<Q` and `1<z²` assumptions in `../ordinary14-aux-root-model-draft/`. No Lean, iPRA endpoint, provider replay, or PDF/JSON/gzip binding is claimed.

The proposed `first_ordinate_large` takes positive internal m, a positive first Pell solution and the explicit **k>2** hypothesis. It reuses `ArithmeticPellFirstNorm.descent` and `two_le_ordinate` in the model: the inverse ordinate cannot be zero, because its inverse norm would force the inverse abscissa to 1 and k=2. Thus the inverse ordinate is ≥2; its norm gives inverse abscissa >m times that ordinate; the forward recurrence yields `k≥8m+4`. The proof does not assume the standard-integer descent transfers without that source theorem.

The other proposed facts work in `DiffRing V` with explicit assumptions. `strong_f_square_large` assumes `c>0`, `i≥1`, `0<Delta<c³`, and the stated strong norm, and derives `f²>c+1`. `strong_Q_gt_one` assumes `c>1`, `i≥1`, and `Q=(i*c²)²`. `signed_square_gt_one` assumes `c>1`, `f²>c+1`, and the exact **signed difference-ring equality** `z+c=f²*t`; it uses `ModelDifferenceRing.one_le_of_pos` to rule out a nonzero ring multiple of f² strictly between zero and f². The variable t need not be a natural model element. These are fact-level hypotheses, not claims that any graph satisfies them.

Still needed for the actual graphs: extract their first/main/strong residuals into the stated model norm equations; prove the scaled main magnitude has a natural square root; prove **k≠2** from its consecutive-square gap (no model proof is supplied here); and, after the large-k lemma, derive `c>1`, `0<Delta<c³` using the literal positive X,Y,eta,zeta parameters. Cast the natural strong norm into the difference ring, bind `Q` and `z+c=f²*(T*c−R)` exactly in the graph, and connect these bounds to `AuxRootBridge.positive_aux_coordinate_iff` and positive `Fin 14` updates. The full graph client, compact ports, provider ancestry and parent/iPRA endpoints remain open.

All proof scripts, elaboration, ordered-ring tactics, definability and resource behavior are untested. The source inventory and bounded Pell, strong-norm and signed-gap controls are not universal/model proofs or a Lean preflight. Any future Lean run requires an independently reviewed coherent source/object/Init provider route, the established disk/resource guard and exclusive allocation.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-aux-root-bounds-model-draft/check_source.py > /tmp/aux-root-bounds-source.json
cmp /tmp/aux-root-bounds-source.json research/ordinary14-aux-root-bounds-model-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-aux-root-bounds-model-draft-independent/`.
