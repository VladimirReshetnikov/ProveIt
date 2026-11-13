# Source-only ring-valued 84↔85 field comparison

`RingComparison.lean` is an **unelaborated, uncompiled source proposal**, not a positive-model witness map, Lean theorem, provider replay, endpoint or external file binding. Its bare imports name the separately drafted literal `P84QcubeGraph` and `P85QcubeGraph` sources in a possible future overlay; those sources and their shared provider chain have not been compiled together.

For arbitrary integer ports and any `CommRing R`, the proposed `transform` changes slot 6 from w to `X=(1+J*beta)*w` and slot 12 from gamma-prime to the **ring difference** gamma-old=`gamma_prime−w`. The five proposed field-evaluation lemmas and `output_eval` compare the transformed 85 graph with the 84 graph. The main carrier's exact polynomial cut is `U*(gamma_prime−w)+(X*Y)*q=U*gamma_prime` under `X=q*w` and `Y=q³*s`; the checker verifies this identity in a free sparse polynomial ring and tests all fields and output on 200 signed assignments.

This ring identity **does not establish that the natural difference is positive**, nor that arbitrary transformed ring values are model elements. An 84→85 model client must first obtain `gamma_prime>w` from that graph's own signed norm, q⁴/exact-index and natural carrier hypotheses, then justify the natural truncated-subtraction cast and positive slot update. The separately source-reviewed `../ordinary14-modified-carrier-gamma-model-draft/` assumes the needed carrier/Pell facts; it does not extract them from the graph. In the other direction, an 85→84 client must derive q|X from the parent model route and actual Mersenne port, construct positive w, set gamma-prime=gamma-old+w, and establish the corresponding ring/natural valuation equality. The separately drafted Mersenne fact is conditional on X's power form and q|3X.

The source `simp`/`ring` field proofs, `Function.update` reductions, generic casts, elaboration and resource use are untested. `check_source.py` pins both literal candidates, verifies the exact graph delta and cut, replays graph-source generators and runs finite controls; it is not a Lean preflight or a proof in arbitrary rings/models. Literal norm/index extraction, provider compatibility and exact source/object/Init routing, compact port binding, remaining parent bridges, and the iPRA endpoint remain open. Before any future Lean run, require independent source/provider prelaunch, the established disk/resource guard and exclusive allocation.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-84-85-ring-client-draft/check_source.py > /tmp/ring-84-85-source.json
cmp /tmp/ring-84-85-source.json research/ordinary14-84-85-ring-client-draft/observation.json
```

Independent source review is recorded in
`../../reviews/ordinary14-84-85-ring-client-draft-independent/`.
