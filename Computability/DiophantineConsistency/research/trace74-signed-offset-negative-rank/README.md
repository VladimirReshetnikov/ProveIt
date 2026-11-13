# Fixed-payload scalar negative-rank obstruction

The signed offset divisibility proposed for the 74 graph, together with the already checked first-index residue *as a bare scalar congruence*, does not by itself force a nonnegative rank. Using the exact retained fixed beta/MC/MF payloads, set `J=1`, `q=beta+1`, `F=q²`, `C=q²+1`. The 74 integer rank cone gives

```
R = -q⁵ + q³ - q² + 1 + MC + q*MF < 0.
```

Set `k=R+1+2*q⁵`, `eta=1`, `zeta=k-1`. The resulting coordinates are positive, and the 74 signed offset cone gives `e=k-R-1=2*q⁵`, divisible by `q⁴`. The fixed MC is even and q is even, so k is even. Choosing the abstract scalar `n=(k mod q⁴)/2` yields `0<n≤k` and `k ≡ 2*n (mod q⁴)`. The strict reverse guard fails. The checker verifies these claims by exact arithmetic on the pinned compressed/raw beta, K0, MC and MF payloads and evaluates only the source graph's `q`, `R`, `k` and `e` cones.

The chosen `n` is **not proved to be the graph's first Pell index** and its Pell recurrence equations are not checked. Other 74 witnesses and the full graph output are not assigned or evaluated. This is not a positive full graph zero, a counterexample to the fixed-port graph guard, or an iPRA result. It shows that offset divisibility and the isolated scalar congruence alone cannot establish the desired natural rank representative; the actual Pell recurrence or additional graph facts must be used. The external payload-to-symbolic-Lean binding is also not proved here.

Run `python3 -I -S -B Computability/DiophantineConsistency/research/trace74-signed-offset-negative-rank/check.py` from the repository root. The author tool exited 0; its inner receipt does not independently capture that outer exit. Checker SHA-256 `258c861381875bbe4a0c1a1e18e1c1c82551412318fa004e66cdff5576e770c2`, stdout SHA-256 `30e2833b3628643ebce110e2a93804ed9b0acd22f959546ba65826d9a32c8816`. The [independent paired scalar audit](../../reviews/trace74-negative-rank-pair-independent/README.md) passed (SHA-256 `9327778dfd0e37768187a69c0612735b99df2ad4184eff4509554d3bad900792`), retaining the distinction between the partial examples and a full graph zero.
