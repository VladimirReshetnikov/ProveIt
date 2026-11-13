# Large F with C≤q and positive B: partial fixed-payload example

This strengthens the separate [large-F partial construction](../trace74-large-f-partial-obstruction/README.md) by also satisfying the scalar sign condition `B=(K0+w)*C-F>0`. Use the exact retained beta/K0/MC/MF payloads and set `J=s=eta=1`, `q=beta+1`, `w=q³`, `P=q¹⁰`, `k=8P+4`, `zeta=k-1`. Define

```
C  = q+3-MC
A0 = q²(q²-1) - C(q²-1) + MC + q*MF
N  = A0-(k-1)
F0 = (-(1+q²)*(N/q)) mod q³
F  = F0+q³.
```

Exact fixed-payload evaluation verifies `2≤C≤q`, `q³≤F<2q³`, negative 74 rank, `q⁴ | e` for `e=k-R-1`, `8P+4≤k` and `2q⁴<c`. Since `wC≥2q³>F` and K0 is positive, the source B cone is strictly positive. The source Dtau and two first-Pell recurrence steps are independently checked as exact sparse polynomial identities over `Z[q]`: `X=q⁴`, `Y=q³`, first index `n=2`, `2*ycoord=k` and `Dtau=xcoord²`. Sparse identities avoid expansion of a multi-million-bit square.

This is a **partial scalar example**, not a full graph zero or a verified full carrier solution. In particular it does not check the second Pell equation/root, V/Z square identities, adjacent quotient, remaining witnesses, graph output or payload-to-symbolic-Lean binding. The positivity of B is one scalar condition, not the full carrier theorem. It does not refute a fixed-port guard theorem or establish an iPRA result. It shows the listed partial facts plus B positivity do not alone imply `F<q`; additional actual graph relations could exclude the assignment.

Run `nice -n 15 python3 -I -S -B Computability/DiophantineConsistency/research/trace74-large-f-positive-carrier-scalar/check.py` from the repository root. Actual author outer session 45707 exited 0 and was fully reaped; its inner receipt does not independently capture that exit. Checker SHA-256 `4c2adc4812244b917e8526fc7eada30220624049ceb026098acae0795e7e3a08`, stdout `eefdecc0549e7eedaff5ca2dcf3e42ffdcba63a8d06eb7fcfa3126b4f0e3a321`. An exploratory first run reached the output step but failed JSON integer-to-string conversion; it is not proof evidence. The [independent scalar audit](../../reviews/trace74-large-f-positive-carrier-scalar-independent/README.md) passed (SHA-256 `1062abb8cc07ccece1741b3f6b029ed53cbf4686d1870a91aeeb3fbfa0853e8c`), retaining all partial-graph and unverified full carrier limits.

The later [odd-ordinate exclusion](../trace74-odd-ordinate-partial-exclusion/README.md) shows that this particular partial assignment cannot satisfy the checked full-graph odd-ordinate consequence, under the stated external interpretation. It does not establish a general bound on F or C.
