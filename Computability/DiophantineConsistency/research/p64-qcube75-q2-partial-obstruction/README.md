# The q²-scale experiment: a partial obstruction

Starting with the 76Y graph, replace `Y := q³*s` by `Y := q²*s` and delete the now-unused `q3` gate. The resulting 75-operation graph allows `q² | Y` without imposing `q³ | Y` by construction. Reversing the coordinate substitution for an arbitrary zero would need to recover the missing divisibility.

The exact natural-port example here satisfies the **full first norm, main residual and transport residual** with `q² | Y` and `q³ ∤ Y`. The original strong norm additionally has a symbolic positive witness, as explained below. **The auxiliary-unit equation is not solved.** This is neither a full modified-graph zero nor a counterexample to existence equivalence, and it makes no fixed-compact44-port claim. The existing old-graph proof of `q³ | Y` uses a different first-factor scaling; it does not automatically apply to this weakened expression.

## Exact partial assignment

For integer `d`, use `(x,y)^e_d` for powers with multiplication `(x,y)(u,v)=(xu+d yv, xv+yu)`. Put

```
q=4; Y=96; X=128; U=9216; a=12384; n=a+2; H=4a+3
D=n²−1; P=X Y²
(t,k)=(2P+1,2)^212_(P(P+1))
(g,c)=(n,1)^322_D
A=U(g−X−a c)/H; R=k−1+A−U
```

The division is exact. The ports are `(beta,K0,MC,MF)=(3,3,R−150,0)` and the specified positive graph inputs are

```
J=1, F=1, alpha=1, z=23, s=6, w=32,
t=t, eta=c−96k, zeta=97k−c, gamma=1.
```

`check.py` executes every retained graph gate through `Lt`, using `Y=q²s`, and checks `A0=1`, `M=Lt=0`, the signs and exact division. The number `Y=96` is divisible by 16 but not 64. The 4686-bit `c` and 4685-bit port `MC` are defined exactly above, not by their hashes; `result.json` records hashes for reproducibility.

## Strong norm can also be met symbolically

Write `(g,c)^c_D = (f,L)`, and put `I=D L` and `i=I/c²`. The exponent is a definite positive 4686-bit integer: explicitly expanding these numbers is computationally impractical. Nevertheless the following exact algebra proves that `i` is a positive integer and the original graph's strong residual `W` is zero:

- `g²−D c²=1` is verified by the script, so multiplicativity of the quadratic norm gives `f²−D L²=1`.
- In the binomial expansion of `(g+c√D)^c`, the `√D` coefficient is divisible by `c²`: its linear term is `c² g^(c−1)`, and all higher terms have at least two factors of `c`. Thus `c² | L`.
- Therefore `I=i c²` for positive `i`, and `I²=D²L²=D(f²−1)`, which is exactly `W=0`.

This symbolic proof is separate from the executable checker; the checker does not expand, evaluate or certify `f`, `i`, or `W`. There is no supplied `T,y` with `Na=1`, and no claim that such inputs exist.

Run from any directory:

```
python3 -I -S -B path/to/p64-qcube75-q2-partial-obstruction/check.py
```

The deterministic output is frozen in `result.json`; the graph source and script are SHA-256 identified.
