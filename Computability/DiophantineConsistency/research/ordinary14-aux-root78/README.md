# Direct auxiliary root: 14 positive inputs, 78 operations, degree 60

This proposed graph has 78 live operations and exact degree 60 at the authenticated compact44 ports. Its positive-zero existence is equivalent to the reviewed 79/60 graph for arbitrary integer ports with `beta>0`. The new positive input `y` takes the place of the old `u`; the other thirteen coordinates are unchanged. This is an external integer argument submitted for independent review, not a Lean/iPRA theorem, PDF/JSON binding, or global minimality claim. Its eventual connection to the named endpoint inherits the 79 graph's external calibration and source/provider qualifications.

## Graph change and witness maps

Let `V=f²*(T*c−R)−c`, `Q=Delta*(f²−1)` and `I=i*c²`. The 79 graph defines `y=V+u` and `Fa=y²−Q*u*(y+V)`. The new graph directly uses positive input `y` and `Fa=y²−Q*(y²−V²)`. The identity `u*(y+V)=y²−V²` holds whenever `y=V+u`, over all integers. The other four residuals are literally unchanged and do not use `u` or `y`. Deleting `y=V+u`, `y+V` and their product, then adding `V²` and `y²−V²`, saves one net operation. The whole output agrees under this substitution, though the positive domains require the proof below.

On a zero of either graph, all five integer-square residuals vanish. The first, main and strong residuals force `|V|>1` independently of the sign of V, the auxiliary input, and the transport guard. The strong residual gives `Q=I²>1`; setting `Fa=1` then yields

```
(Q−1)*(y²−V²) = V²−1 > 0,
```

and therefore `|y|>|V|`. For an old positive zero, `y=V+u>V`; together with `|y|>|V|` this implies `y>0`. Conversely, for a new positive zero, `y>|V|>=V`, so `u=y−V>0`. The substitution preserves all residuals and all other coordinates in both directions. Neither map assumes the old graph already has a zero when analysing the new graph; neither assumes `V>0`, a decoder, rank bounds, or a canonical witness.

## Why the other residuals exclude |V|≤1

All inputs are positive and beta>0, so `q=1+J*beta`, `X=q*w` and `Y=q³*s` are positive. Write `m=X*Y²`, `k=eta+zeta>=2`, `ell=m*k`, `c=eta+k*Y`, `a=XY+Y`, `Delta=(a+2)²−1` and `U=Y*q²>0`. The unchanged first and main residuals yield

```
tau² = 1+m*(m+1)*k²,       Dstar² = U²*(1+Delta*c²).
```

The second equation implies `U | Dstar` by prime valuations, so `1+Delta*c²` is an integer square. If `k=2`, positivity forces `eta=zeta=1`, giving `c=2Y+1` and `1<c<2(a+2)`. The supposed square lies strictly between `((a+2)c−1)²` and `((a+2)c)²`, impossible. Thus `k>2`. The reviewed elementary Pell descent in `../ordinary13-folded-root86-negated-positive-bt/` applies to the displayed first equation and gives `k>=8m+4`; its proof is also included in that packet. It follows that

```
c = eta+kY > 8XY³,
a+2 = Y(X+1)+2 <= 4XY,
Delta < 16X²Y² < c³.
```

The strong residual is `I²=Delta*(f²−1)` with `I=i*c²>=c²`. Since `Delta>0` and `Delta<c³`, this implies `f²−1>=c⁴/Delta>c`, so `f²>c+1`. But `f²` divides `V+c`; if `V` were −1, 0 or 1, then `V+c` would be one of the positive integers `c−1,c,c+1`, each strictly less than `f²`. This contradiction proves `|V|>1`. Also `I>=c²>1`, so `Q=I²>1`, as used above. No condition on `R`, `T*c−R`, or the sign of `V` is needed.

## Count and exact degree

The checker verifies the full source delta, topological order and liveness of all 78 gates, all 14 inputs and four fixed ports. It checks 160 signed substitution controls and reproduces the reviewed parent and Pell-descent review receipts. There are 42 multiplications, 19 additions and 17 subtractions.

With port numerals fixed, `deg X<=2`, `deg Y<=4`, `deg c<=5`, `deg Delta<=12`, `deg Q<=14`, and `deg V<=8`. Thus the new auxiliary residual has degree at most 30. The first, main, strong and guard residuals retain bounds 22, 30, 22 and 3 from the reviewed 79 graph, including its main-residual cancellation, so the sum of squares has degree at most 60. Evaluating the complete new graph along the all-inputs-equal ray at the hash-authenticated actual ports modulo 1,000,000,007 gives degree 60 and leading coefficient 619528110; hence the specialized integer degree is exactly 60.

```
python3 -I -S -B research/ordinary14-aux-root78/check.py > /tmp/aux-root78.json
cmp /tmp/aux-root78.json research/ordinary14-aux-root78/result.json
```

The finite controls and degree ray do not replace the unbounded zero-set proof. No Lean was run.

Independent mathematical review is recorded in
`../../reviews/ordinary14-aux-root78-math-independent/`.
