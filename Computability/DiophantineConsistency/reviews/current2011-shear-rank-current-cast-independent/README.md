# Independent review of generic and current-port rank-cast drafts

The source-level cast formulas and their hypotheses agree with the pinned
natural and signed carrier definitions. No concrete mathematical or interface
mismatch was found. Both drafts, their local import names, and all Lean
simplification and provider resolution remain unelaborated.

For a natural-model embedding `ι`, if `b<=a`, then `a−b+b=a`; embedding
this equality gives `ι(a−b)=ι a−ι b` in the difference ring. The generic
rank lemma applies that identity only under its explicit three hypotheses
`1<=q`, `F<=q` and `1<=q²`, and maps the remaining sums and products.
Its gap lemma correctly obtains `F<=q` from `0<q−F−alpha`. The separate
c equality requires only multiplication and addition. These are mathematical
checks of the proposed source, not Lean elaboration.

The current-port source gives the integer tuple
`[beta,K,lowPort,highPort+beta]`; the proposed model-natural tuple uses the
same order and a single high-port beta shift. The proposed finite-index proof
compares the four integer casts to their model-natural embeddings. With
`q=beta*J+1`, the signed first rank factor `beta*J` equals `q−1`;
the remaining signed factors and mask terms agree with the generic rank
formula. The shifted valuation is the same one used by the forward-index
client, and `core_c_cast` uses the corresponding y-independent c field.
The final theorem still relies on the unelaborated forward natural bound,
the two proposed exact casts and their provider assumptions.

The independent checker pins both drafts and the relevant current tuple,
carrier, model embedding and natural-rank sources. It checks bounded current
port/valuation instances and an `F>q` negative control, but those checks do
not prove model casts. In particular, `fin_cases`, tuple simplification,
`rw` occurrence selection, `map_natCast`, all `simp` steps and the final
source composition need actual Lean checking. The fixed tuple's full
provider/axiom ancestry, literal child evaluator and witness maps remain
separate obligations.

Reproduce all three receipts from `Computability/DiophantineConsistency`:

    set -o pipefail
    timeout 30s python3 -I -S -B research/current2011-shear-rank-cast-generic-draft/check.py | cmp - research/current2011-shear-rank-cast-generic-draft/result.json
    timeout 30s python3 -I -S -B research/current2011-shear-current-port-cast-draft/check.py | cmp - research/current2011-shear-current-port-cast-draft/result.json
    timeout 30s python3 -I -S -B reviews/current2011-shear-rank-current-cast-independent/check.py | cmp - reviews/current2011-shear-rank-current-cast-independent/receipt.json

No Lean process, build, staging or reviewed-file mutation was performed.
