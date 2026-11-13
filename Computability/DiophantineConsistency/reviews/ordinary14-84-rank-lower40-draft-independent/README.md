# Independent source review: 84 rank lower bound 40

The scalar source explicitly applies model discreteness to the strict guard
gap, reconstructs natural subtractions only after bounds, and derives
`q−1≥2`, `q−F≥2`, the first rank factor at least 5 and `q²−1≥8`. Product
monotonicity then gives `R≥40`; nonnegative MC and MF require no upper bounds.
The own-zero client applies the 84 guard gap with its stated beta/K casts and
positive valuation. The prior source-level concern about using a discrete gap
without exposing its successor bound is addressed in the pinned revised draft.

The checker pins the revised source, replays author and independent natural
rank receipts, and tests a finite grid, assumption boundaries, and a sharp
guard-only R=40 example. This example is not a full graph zero. Source and
finite controls are not a Lean proof: elaboration, exact-index hypotheses,
provider compatibility, external files and iPRA remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-rank-lower40-draft-independent/check.py > /tmp/rank-lower40-independent.json
cmp /tmp/rank-lower40-independent.json reviews/ordinary14-84-rank-lower40-draft-independent/result.json
```
