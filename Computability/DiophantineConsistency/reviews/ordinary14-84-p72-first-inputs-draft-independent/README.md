# Independent source review: 84 P72 first inputs

The three imported clients are applied to the same 84 own-zero and valuation,
with the same beta/K/MC/MF casts and required mask bounds. The lower-40 source
bound implies the stated lower bound 26, and the rank window supplies
`R+1<q⁴`. Applying the latter only to the rank-side remainder yields
`(2n)%q⁴=R+1`; the first-index and residue witnesses are retained unchanged.

The checker pins all three source interfaces, replays the author and independent
dependency receipts, and checks finite examples including `2n≥q⁴`, for which
the first-index remainder cannot simply be removed. This is source and finite
review only. Auxiliary norm, remaining P72 premises, Lean elaboration,
provider compatibility, external file binding and the iPRA endpoint remain
open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-p72-first-inputs-draft-independent/check.py > /tmp/p72-first-inputs84-independent.json
cmp /tmp/p72-first-inputs84-independent.json reviews/ordinary14-84-p72-first-inputs-draft-independent/result.json
```
