# Independent source review: 84 first-index residues

Positive Q supplies `1≤Q` and hence `(Q−1)+1=Q`. This rewrites both the
first-norm discriminant and the two outputs of `solution_residues` at
parameter `Q−1`. The resulting existential witnesses satisfy the stated
coordinate equations, `tau=1+2Qr`, and `k=2n+4Qs`. The source does not
identify n with the rank.

The checker pins the classification and first-norm interfaces, replays the
author and independent first-norm receipts, and exercises finite Pell
recurrences and both nonnegative residue quotients. This is source and finite
review only: no Lean elaboration, exact rank index, provider compatibility,
external file binding or iPRA endpoint is established.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-first-index-residues-draft-independent/check.py > /tmp/first-residues84-independent.json
cmp /tmp/first-residues84-independent.json reviews/ordinary14-84-first-index-residues-draft-independent/result.json
```
