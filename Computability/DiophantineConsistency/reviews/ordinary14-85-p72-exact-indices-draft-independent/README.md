# Independent source review: direct 85 P72 exact-index composition

All four source clients use the same 85 own-zero and valuation. Against
`P72Exact.indices_ordinary`, the arguments are q, direct slot-6 X, Y, k, R,
the main d, c, a, slot 7, slot 4 as i-prime, slot 3 as f, slot 5 as T,
slot 11 as u, first n and s, q⁴ as modulus, main m, and slot 9 as eta. The
discrete guard gap yields q≥3; strong and auxiliary norms match the source
hypotheses. The same d and the old `X*Y*q` balance are retained. No `q | X`
or other graph zero is assumed.

The checker pins source interfaces, replays author and four independent
dependency receipts, and checks finite auxiliary/delta shapes. This is source
review, not an elaborated Lean theorem or arbitrary-model proof. Definitional
equalities, tactics and providers remain unverified; power recovery, compact
port/mask binding, the reverse map, external file binding and iPRA are open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-p72-exact-indices-draft-independent/check.py > /tmp/p72-exact-indices85-independent.json
cmp /tmp/p72-exact-indices85-independent.json reviews/ordinary14-85-p72-exact-indices-draft-independent/result.json
```
