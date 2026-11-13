# Actual residue-graph exact-index fact client

This source-only client proposes assembling `P72Exact.indices_ordinary` from
the actual 90-row residue graph's early-index draft. **No theorem, tactic,
import or provider has been Lean checked.** Its input is the exact residue
literal zero, not an original free-J literal-zero premise or an equality to
that graph's old first root.

The draft calls the proposed actual-main rank-congruence and actual-first-norm
client, obtains the early recurrence index, and supplies `q⁴` as the modulus
for `indices_ordinary`. It explicitly retains:

- represented natural ports and positive J, beta, X, plus `F+alpha<q`;
- the rank window and the **stronger `R≥26`** premise, rather than silently
  substituting the earlier `R≥24` bound;
- a natural main root g and its exact ordinary main norm;
- a main index with `ycoord mainIndex a=c`;
- a positive ordinary strong witness `i'`, positive f, its exact strong norm,
  and the complete old-auxiliary `absdiff` equation with a natural u.

`main_index_of_natural_norm` separately proposes the existing Pell
classification call that constructs such a main index from the explicit norm;
it does not itself extract g or the norm from a graph zero. The source's
exact-index conclusion remains conditional on all the listed facts.

`P72Exact.indices_ordinary` itself does **not** assume the later Bézout
condition. Accordingly this client does not claim `q∣X`, exact calibration,
or a parent bridge. The later `P72Exact.exact_ordinary` additionally needs its
explicit main-balance conditions and `Bez q H 1`; neither is supplied here.
The strong/auxiliary witness conversion, compact fixed-port and kernel byte
bindings, parent endpoint, provider ancestry, physical PDF and internal iPRA
proof remain separate obligations.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-exact-index-model-draft/check.py | cmp - research/ordinary13-residue-exact-index-model-draft/receipt.json
```

The read-only checker pins named sources, reruns the earlier fact-client
checks and controls the exact discriminant algebra on finite natural inputs.
It does not execute Lean, validate proof tactics or authenticate providers.
