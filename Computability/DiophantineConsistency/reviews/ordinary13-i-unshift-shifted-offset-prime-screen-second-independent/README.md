# Independent review: corrected shifted-offset prime screen

The reviewed `research/ordinary13-i-unshift-shifted-offset-prime-screen/` gives the correct completed-square constant and correct classifications for its stated fixed compact tuple, J=1 and exact power/index matching. It does not decide graph-zero existence or rule out other J, rank offsets, or witness constructions.

Write `d=L−h`, `m=n+d` and assume the matching equation `(h+1)n=(L−h)(2L−h+1)` and the exact rank `R=2n−1`. Independent exact polynomial expansion gives

```text
(4L+1−3h)² − (h+1)*(h+5+4R)
  = 8*((L−h)*(2L−h+1)−(h+1)*n).
```

Thus the right-hand side of the completed-square condition contains **h+5**, and for h=1 becomes `8R+12` as in the earlier prime obstruction. A nonsquare value modulo the pinned prime is a valid contradiction; a square value is only a necessary-condition pass.

The mod-3 rank condition `R≡0` requires `n≡2 mod 3`. Independent enumeration of h, L and n modulo 9 shows that matching is impossible for `h≡0,2,3,5,6 mod 9`; this is the prior mod-3 exclusion translated from its offset convention. The remaining h in 1 through 30 are exactly the 13 entries in the reviewed screen.

The checker reproduces the prior independent source-digit and primality review, then computes each of the 13 Legendre symbols using a separate binary Jacobi algorithm, cross-checking Euler's criterion. It obtains nonsquares for `1,7,10,16,19,26,28` and square-or-zero passes for `4,8,13,17,22,25`, exactly as reported. No pass establishes a compatible Pell witness, graph zero or equality of zero sets. The fixed J=1 prime residue must not be reused for arbitrary J.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-i-unshift-shifted-offset-prime-screen-second-independent/check.py | cmp - reviews/ordinary13-i-unshift-shifted-offset-prime-screen-second-independent/receipt.json
```

The checker pins and reproduces both earlier receipts and verifies the polynomial and finite residue calculations. It does not execute Lean, build providers, audit axioms or prove an iPRA result.
