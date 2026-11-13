# Fixed-payload negative rank with first-Pell index two

Even imposing `n≥2` on the first Pell index, the first Pell recurrence and signed offset divisibility alone do not force nonnegative 74 rank. For the exact retained beta/MC/MF payloads set `J=F=w=s=eta=1`, `q=beta+1`, `P=q⁷`, `k=8P+4`, `zeta=k-1`, and

```
A = q*(q-1)*(q²-1) + MC + q*MF
C = ((3-A)*(q²+1) mod q⁴) + q⁴.
```

The partial 74 rank and offset cones give `R=A-C*(q²-1)<0`, `R≡3 (mod q⁴)`, and `e=k-R-1` divisible by `q⁴`, with all assigned witnesses positive and `F+C>q`. The actual first Pell base is `B=2(P-1)+1`. Starting at `(x0,y0)=(1,0)`, two recurrence steps give `x2=8P²+8P+1` and `y2=4P+2`, with `2*y2=k`. The candidate graph's `Dtau` satisfies `E=x2²=1+P(P+1)k²`. The checker verifies these last equalities as exact sparse polynomial identities over `Z[q]`, then applies them to the actual decoded q; it verifies the R/e cones by direct integer arithmetic on the exact fixed payload. This avoids expanding the multi-million-bit square.

For this same tuple, the separately pinned `check-size.py` also verifies the proposed guard-independent fold size consequences: `8*P+4≤k` holds with equality, and `2*q⁴<c` for `c=k*q³+1`. The size checker SHA-256 is `17a6181b78d1bb0e8f63ef00003b373dd83cc6096e163805f68d084d885f2639`; its captured `size-stdout.json` SHA-256 is `ff310eaf0e9361c03c525e5627afb085051c77294d60576ae0e0bdebbd6854a6`. The author saw its outer tool exit 0; the inner size receipt does not independently capture that exit.

This is a **partial scalar example**, not a full graph zero. It does not check the second Pell equation or root, adjacent/carrier factors, other witness coordinates, graph output or the payload-to-symbolic-Lean binding. Additional graph constraints could rule it out; it is not a fixed-port guard counterexample or iPRA result. The two [earlier](../trace74-signed-offset-negative-rank/README.md) [examples](../trace74-first-pell-negative-rank/README.md) remain separate.

Run `nice -n 15 python3 -I -S -B Computability/DiophantineConsistency/research/trace74-second-pell-negative-rank/check.py` from the repository root. Author session 41307 exited 0 and was fully reaped; the inner receipt does not independently record that outer exit. Checker SHA-256 `5b606d5a9864be51eed36d7bbb11812ef3e4928500eb732b802741a86290a9e4`, stdout SHA-256 `061de664dfb79a53a55e143f29715557d1a8319be2c968b12545e7746235d8f8`. The [independent scalar audit](../../reviews/trace74-second-pell-negative-rank-independent/README.md) passed (SHA-256 `dd778f7fcb0f744588c1b957f312830087424a906bad46665b8472ab1afad433`), retaining the partial-graph and unverified second-Pell/carrier limitations.
