# Fixed-payload negative rank with the first Pell recurrence

Even adding the actual first Pell recurrence to signed offset divisibility does not, on its own, force nonnegative 74 rank. For the retained fixed beta/MC/MF payloads, set `J=F=w=s=eta=zeta=1`, `q=beta+1` and

```
A = q*(q-1)*(q²-1) + MC + q*MF
C = ((1-A)*(q²+1) mod q⁴) + q⁴.
```

The partial 74 integer graph gives `R=A-C*(q²-1)<0`, `R≡1 (mod q⁴)`, `k=2`, and `e=k-R-1=1-R`, so `q⁴ | e`. All assigned witnesses are positive and `F+C>q`. The source graph's `X=q`, `Y=q³`, `P=X*Y²=q⁷`, and `E=Dtau` satisfy the actual first Pell identity `E=(2P+1)²=1+P(P+1)k²`. At index `n=1`, one step of the first Pell recurrence gives `xcoord(1,2(P-1)+1)=2P+1`, `ycoord(...)=1`, so `2*ycoord=k` and `0<n≤k`.

This is an **exact partial scalar construction**, not a full graph zero. It does not check the second Pell equation or root, the adjacent/carrier factor, other witness coordinates, graph output or the source-to-Lean fixed-port binding. In particular, a separate graph argument might force the first index to be at least 2 and rule out this assignment. No fixed-port guard failure or iPRA conclusion follows. The weaker [separate obstruction](../trace74-signed-offset-negative-rank/README.md) uses an arbitrary congruence witness without asserting first Pell recurrence.

Run `python3 -I -S -B Computability/DiophantineConsistency/research/trace74-first-pell-negative-rank/check.py` from the repository root. Author tool session 54011 exited 0 and was reaped; the inner receipt does not independently capture the outer exit. Checker SHA-256 `1ceb41fa9cff6cefb59e9e0ff3c5e67b563530f9a314f8df95eb8f2193f579eb`, stdout `f709979a9f522bbd3b33b73a33ed9c938af98a9f5c0844af5f127cdcfb70121e`. The [independent paired scalar audit](../../reviews/trace74-negative-rank-pair-independent/README.md) passed (SHA-256 `9327778dfd0e37768187a69c0612735b99df2ad4184eff4509554d3bad900792`), retaining the distinction between the partial examples and a full graph zero.
