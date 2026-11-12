# Independent source review: 84 natural rank

The natural rank formula matches the signed rank source expression after
casting the MC and MF ports. Its two natural subtractions require distinct
bounds: `F≤q` for `q−F`, and `1≤q²` for `q²−1`. The own-zero client obtains
the former from the reviewed 84 guard gap and the latter from
`q=1+J*beta≥1`. Both beta/K casts used by the guard and both MC/MF casts used
by the rank formula are explicit.

The checker pins the source interfaces, replays the author and independent
guard review, and compares natural and signed rank expressions on a finite
grid, including the subtraction boundary and a counterexample if `F≤q` is
omitted. These are source and finite controls only; no Lean elaboration, rank
window, provider compatibility, external binding or iPRA endpoint follows.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-natural-rank-draft-independent/check.py > /tmp/natural-rank84-independent.json
cmp /tmp/natural-rank84-independent.json reviews/ordinary14-84-natural-rank-draft-independent/result.json
```
