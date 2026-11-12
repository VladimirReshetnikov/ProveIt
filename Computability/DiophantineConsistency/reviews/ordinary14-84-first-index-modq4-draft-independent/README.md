# Independent source review: 84 first-index congruence

Both source clients are applied to the same positive valuation and the same
84 graph zero, with the four port casts retained. The model modulus q⁴ is
positive. From `Y=q³*slot7`, the witness
`4*X*q²*slot7²*s` proves `q⁴ | 4*X*Y²*s`. The magnitude-to-modulo lemma is
applied in the correct `(R+1,k)` order; removing the known multiple and
reversing the equality yields the stated first-index congruence.

The checker pins the interfaces, replays the author and independent dependency
receipts, and tests both signs of the natural difference on finite inputs.
This is source and finite review only. It does not remove the modulus or
establish a rank window, exact index, Lean elaboration, provider compatibility,
external file association or iPRA endpoint.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-first-index-modq4-draft-independent/check.py > /tmp/first-modq4-84-independent.json
cmp /tmp/first-modq4-84-independent.json reviews/ordinary14-84-first-index-modq4-draft-independent/result.json
```
