# Independent source review: fresh 86 first root

With the explicit `Y=q³s` and `tau²=1+ell(ell+k)` equations, replacing
slot 8 by `P+tau+s` makes the 86 signed first root exactly `−M*tau` and hence
its first residual zero. The original root's sign and any comparison between
it and s are irrelevant. The four nonfirst fields ignore slot 8, so their
own-zero values survive; the five-square reconstruction uses the correct
`aux−1` field and order. Positivity of the eventual 85 witness is a separate
client.

The checker pins the source interfaces, replays the author and independent
field review, and tests both original root branches on finite partial first
norms. These are not full graph-zero witnesses. This is source review only;
Lean elaboration, provider compatibility, external-file binding and iPRA
remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-86-fresh-root-draft-independent/check.py > /tmp/fresh-root86-independent.json
cmp /tmp/fresh-root86-independent.json reviews/ordinary14-86-fresh-root-draft-independent/result.json
```
