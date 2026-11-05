# A partial obstruction to freeing the strong-index carrier

The 76Y graph computes `I=i*c²` and then uses `I²` in the strong residual
`W=I²−Delta*(f²−1)`. A possible gate saving would replace the positive `i`
with an independent positive `I` and omit the multiplication `i*c²`.
Recovering the old witness by this coordinate map requires `c² | I`. The two
scalar norms and transport, even with actual positive q-cube parameter
relations, do **not** imply that divisibility.

For the exact positive partial assignment

```
beta=2, J=F=alpha=z=w=s=1, K0=2, eta=zeta=4,
q=3, Y=27, X=3, a=108, H=435, Delta=12099,
k=8, c=220, g=24199, f=110, I=12099,
```

we have `q=beta*J+1`, `Y=q³*s`, `X=w*q`, `c=k*Y+eta`, transport
`(K0+w)*(q−F−alpha)−F−z*(q−1)=0`, and both scalar norm equations

```
g² = 1 + Delta*c²,       I² = Delta*(f²−1).
```

But `c²=48400` does not divide `I=12099`. Thus these particular facts
cannot justify the direct reverse coordinate map for arbitrary natural
ports. This assignment is **not a graph zero**, and it does not disprove
zero-existence equivalence at any fixed ports:

- `U=Y²=729` and `b0=X+a*c=23763`. If the main residual vanished,
  its carrier would satisfy `Dstar²=U²*g²`, so over the integers
  `Dstar=±U*g`; since `Dstar=U*b0+H*gap`, one of
  `U*(g−b0)` or `U*(−g−b0)` would be divisible by `H=435`. Their actual
  residues are respectively `294` and `132`.
- The first residual would require a square root of
  `ell*(ell+k)+1=306249985`, where `ell=X*Y²*k=17496`. That integer lies
  strictly between `17499²` and `17500²`.

[`check.py`](check.py) verifies all arithmetic above by exact integer
operations and rejects optimized Python. Its captured
[`result.json`](result.json) gives the same concrete observations; the
verifier constructs no complete graph zero and is not a Lean proof. Run:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-free-strong-index-obstruction/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `da690de07652dbdd0965469813475f3ec738a4cfa357a72c0e94e1cf9fcf2d9d` |
| `result.json` | `0c86a11951c5f72f965d6832d0aebb4ace4d3d166c1a34c1f980bf723a47e293` |
