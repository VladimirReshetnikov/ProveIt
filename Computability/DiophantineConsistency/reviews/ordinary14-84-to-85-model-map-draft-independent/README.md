# Independent source review: positive 84 to 85 map

The composition takes the P72 index witnesses and carrier balance from the
same positive 84 graph zero. With `Y=q³*slot7`, `U=Y*q²` and
`W=4*X*q*slot7*s`, the residue term satisfies `U*W=4*X*Y²*s`, so the exact
first-index equality gives `k=R+1+U*W`. The main-index equality `m=R` aligns
both returned Pell coordinates with R. The same natural balance, positive
scale and ordinate, q bound, coordinate identities and `R≥3` are then supplied
to the gamma-growth interface, and the resulting `w<gamma` goes to the
conditional positive 84-to-85 map.

The checker pins the three reviewed interfaces, replays author and independent
dependency receipts, and checks finite quotient identities. This is a source
composition review, not an elaborated Lean theorem or a proof of the reverse
direction. Provider compatibility, concrete port/mask binding, iPRA endpoint
and external file/PDF interpretation remain separate.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-to-85-model-map-draft-independent/check.py > /tmp/model-map84to85-independent.json
cmp /tmp/model-map84to85-independent.json reviews/ordinary14-84-to-85-model-map-draft-independent/result.json
```
