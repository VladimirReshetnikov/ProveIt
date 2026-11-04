# Guard-free upper bound for the signed 74 rank

Write `q=beta*J+1` and use the actual 74 rank expression

```
R = (q(q-F)-C)(q²-1) + (MC+q MF)J.
```

For natural numbers `beta,MC,MF` and positive integers `J,F,C`, with `MC<beta` and `MF<2 beta`, the exact identity

```
q⁴-q³-q-1-R
  = [q(F-1)+(C-1)](q²-1)
    +(q+1)(J-1)
    +J[(beta-MC-1)+q(2 beta-MF-1)]
```

has a nonnegative right side. Consequently **`R+q³+q+1≤q⁴` holds even if `R` is negative**, without the individual bounds `F<q`, `C≤q`, the guard `F+C<q`, or a graph-zero hypothesis. The same algebra can be formulated in an arithmetic model's ordered difference ring; that internal theorem is not claimed here.

`check.py` verifies the identity as exact sparse integer polynomials after substituting `q=beta*J+1`, pins the Lean graph source, and checks the source snippets of the rank expression. Its scalar negative-rank example has positive `J,F,C` and satisfies the stated port inequalities; it is not asserted to be a 74 graph zero. The script does not parse the entire graph, establish fixed-port payload binding, or replace a Lean proof.

Run `python3 -I -S -B research/trace74-signed-rank-upper-bound/check.py` from `Computability/DiophantineConsistency`.
