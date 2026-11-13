# Independent review: natural 85-operation graph

The two altered cuts agree as exact integer-polynomial identities, and only
the claimed two parent rows are removed. Their old uses are exclusively the
claimed cuts; all other shared row definitions agree, so the output agrees
over every commutative ring. Both DAGs are topologically valid, and all 85
gates, 14 variables and four ports of the candidate are live. The 85 count is
an explicit upper bound, not a minimality result.

At the four externally authenticated P72/P115 payloads, this checker
independently computes the full diagonal polynomial modulo 1,000,000,007:
degree 107 with nonzero leading coefficient 419359493. This gives a degree
lower bound. The degree upper bound 107 is inherited from the replayed 86/88
certificates; the author receipt and dependency replay are reproduced.
Agreement with the natural-shifted parent holds by the separately reviewed
86 bridge. These are external arithmetic and graph checks, not a Lean
elaboration, iPRA theorem or internal raw/gzip/JSON/PDF binding.

Run from the project root:

```
python3 -I -S -B reviews/ordinary14-root74-natural-cancel85-independent/check.py | cmp - reviews/ordinary14-root74-natural-cancel85-independent/result.json
```
