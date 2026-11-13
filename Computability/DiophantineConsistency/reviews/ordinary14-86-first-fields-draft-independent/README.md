# Independent source review: 86 first and other fields

The proposed first evaluation matches the 86 signed pair
`(M*P+b*Y,M*r)`, its square and the natural radicand. The own-zero
five-square extraction has the correct field order and `aux−1` convention.
The four other field DAGs do not depend on slot 8, so the stated root update
leaves them unchanged. The beta cast remains explicit.

The checker pins the literal graph and five-square source, independently
checks dependency cuts and signed finite evaluations, and replays the author
and independent graph receipts. This is source and finite review only: the
quotient, witness maps, Lean elaboration, provider compatibility, file binding
and iPRA endpoint remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-86-first-fields-draft-independent/check.py > /tmp/first-fields86-independent.json
cmp /tmp/first-fields86-independent.json reviews/ordinary14-86-first-fields-draft-independent/result.json
```
