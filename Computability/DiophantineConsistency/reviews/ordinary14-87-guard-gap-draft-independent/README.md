# Independent source review: 87 own-zero guard gap

The source extracts the 87 graph's guard from its own five-square zero, with the auxiliary field shifted by one. Its literal guard is `(q−F−alpha)(X+Kq)−F−(J beta)omega`. Positivity of F and X and nonnegativity of the other natural terms force `F+alpha<q`. Both beta and K port casts are explicit; no 86 zero is assumed. This does not show the separate reverse-map bound `C*K<omega`.

The checker pins and replays the author receipt and checks bounded guard-zero cases. This source is not Lean-elaborated. Run `python3 -I -S -B check.py` and compare with `result.json`.
