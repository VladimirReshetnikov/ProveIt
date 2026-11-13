# Early positivity of the free-J ordinary-tail coordinate

In an arbitrary `IΣ₁` model, `FreeJGraphVBound.graph_bound` proves the
following for the **exact 95-operation free-J graph**, not the distinct
100-operation restricted-J graph. Let the four natural ports be `p`, let
`v : Fin 12 → V`, and assume

```
0 < p₀,       p₂ < p₀,       p₃ < 2p₀,
∀j, 0 < vⱼ,   InternalZero (literal (j ↦ (pⱼ : ℤ))) v.
```

The port inequalities are model inequalities after casting the natural ports
into `V`. Set `c=v₈+v₆(v₈+v₉)` and let `z` be the signed-pair evaluation
of `graphV`. The theorem's conclusion is

```
1 < c  ∧  z.2+c < z.1.
```

Thus the actual signed graph expression `V` is strictly greater than
`c>1`: the second inequality is an ordered statement about the pair, not a
natural truncated subtraction masquerading as signed evaluation. The
formula and order of graph operations are pinned by `shape`, proved by
reflexivity: `(core p).pc = graphQ * (graphV p * graphV p) - 1`. In
particular, `graphV` is the expression used in the ordinary tail's `QV²-1`.

The proof uses the separately established first-factor transport and
`FreeJEarlySize.early_size`. The latter obtains `2R<c` before recovery of
the ordinary strong norm. No ordinary norm, exact final rank, fixed-port
calibration, or checker theorem is an assumption. The first-factor result
also gives `F+α<q`, which implies `F<q`: `R_eval` uses this to connect the
literal graph's **signed** `q-F` to the truncated natural subtraction in
the early-size theorem. `V_eval` then transports the graph's signed-pair
semantics to `(f²Tc, f²R+c)`. Finally `simple` shows `2c<f²(Tc-R)` from
positive `T,t` and `2R<c`, and `graph_bound` transports that inequality to
the signed graph pair. The proof does not use the later strong norm to
justify the early bound.

The hypotheses are material. For example, with `c=3`, `R=2`, `T=1`, and
`t=1`, one has `f²(Tc-R)-c=1<c`, so `2R<c` cannot simply be dropped from
the generic size lemma. When `q=2,F=3,α=1,J=1,MC=MF=0`, the signed graph
`R` equals `0` while the natural-subtraction expression equals `3`;
therefore `F<q` cannot be omitted from their identification. These are
small arithmetic counterexamples to over-generalized helper claims, not
solutions of the literal zero equation.

## Bounded evidence and limitations

`replay.py` builds just this source against the historical early-size parent;
it does **not** rebuild the full parent. It checks the frozen source and
parent-receipt hashes, parent object hashes, generated sibling objects,
seed links, pinned parent inputs and absent companions before and after
compilation. It creates a new symlink overlay without mutating the parent,
checks the direct imports, and refuses output replacement. The command is
bounded by Lean's `-M3000`, `-j1`, and a 120-second subprocess timeout.
Run it where the historical paths in the script still exist:

```
python3 replay.py --output /tmp/new-freej-vbound --receipt /tmp/new-freej-vbound.json
```

The recorded invocation actually exited `0` and printed
`PASS_BOUNDED_FREEJ_GRAPH_V_BOUND
31e4f1f541b437b28d37b55e03ea6194d27bf4c4c4009ed3f1bbffefdc453897`.
The [receipt](replay-receipt.json) records the exact compiler invocation,
stdout, object hash, checked parent inputs, and direct dependencies. The
five printed axiom reports do not include `sorryAx`; the main theorem uses
`[propext, Classical.choice, Quot.sound]`.

This is a single-author **model-level** overlay using a historical parent,
not an independent full-project replay, dynamic or package-transitive audit,
formal interpretation of the exact compact44 ports, or an object-level iPRA
derivation. The ordinary-tail signed-ring identity, nonzero denominator,
reduced-denominator descent and extraction of the strong norm still need
separate proofs; this theorem supplies an early positivity premise for that
work. The earlier integrality analysis's description of `V>c>1` as open is
superseded by this conditional model result, subject to these limits.
