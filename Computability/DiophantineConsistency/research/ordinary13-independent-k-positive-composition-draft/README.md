# Independent-k positive-coordinate composition: source proposal

This isolated, **unelaborated** source composes the proposed fixed-compact child bindings and natural rank representation to draft

```
InternalZero (graph intPorts).output v  →  0 < v 10.
```

Slot 10 is the new independent k, and `intPorts` is the exact fixed symbolic compact tuple. The source retains no extra theorem parameter asserting rank representation: it proposes to derive that fact from the actual child zero and a temporary assumption k=0. **This is not an established Lean theorem or an iPRA endpoint.** All imported source claims, including graph-unit extraction, exact child first/main graph bindings, compact casts, first-rank helper and natural-rank representation, are unelaborated and lack a coherent provider or axiom replay.

The draft chain is explicit:

1. At an actual fixed-child zero, the child J-positive source and fixed port client provide positive J and beta. Under k=0, the child graph-fact source proposes the signed first norm.
2. The separate rank-representation source proposes `F<q` from that norm, including when `q−F−alpha≤0`, with no use of k positivity. Its existing generic natural-rank interface needs only F≤q.
3. `rankRing_eq_expr` proposes the missing equality between the graph client's signed rank and the separately generated R-row expression. The checker independently confirms the equality of their expanded integer polynomials, while Lean's simplification, casts and ring tactic are not checked.
4. The prior graph-fact client's `zero_k_impossible_of_rank_representation` then yields the contradiction. The final proposed natural-order step turns nonzero k into positive k.

**Known inherited source issue:** independent review of `IndependentKRankRepresentationDraft.rank_representation` flagged that its final `linear_combination h` likely needs the opposite equality orientation because the imported helper states `ι(rank)=signed`, whereas the target is `signed=ι(rank)`. This packet pins and imports that unchanged source and cannot establish the result until that issue and any other elaboration defects are resolved. A future repaired alternative must be selected and this packet's pins refreshed; no repair is silently assumed here. The parent graph unit/norm draft and all other dependencies may contain additional unobserved issues.

The checker reproduces the rank, graph-fact and fixed-port receipts, checks argument order and source dependency names, independently verifies the signed-rank polynomial identity and exercises both first-norm branches on finite naturals. Those checks do not validate `InternalZero` extraction, arbitrary-model arithmetic, tactics, transitive imports, an axiom set, a parent-child zero correspondence or the equation's PDF binding. In particular, positive k alone does not establish eta≤k.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-independent-k-positive-composition-draft/check.py | cmp - research/ordinary13-independent-k-positive-composition-draft/receipt.json
```
