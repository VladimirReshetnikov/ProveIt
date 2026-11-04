# Fixed-payload partial example with bounded C and large F

For the exact retained beta/MC/MF payloads, there is a **partial scalar assignment** satisfying `0<C≤q` while violating `F<q`, even after imposing the already established signed offset congruence, first Pell recurrence at index 2 and the two guard-independent size inequalities. Set `J=w=s=eta=1`, `q=beta+1`, `P=q⁷`, `k=8P+4`, `zeta=k-1`, and

```
C  = q+3-MC
A0 = q²(q²-1) - C(q²-1) + MC + q*MF
N  = A0-(k-1)
F0 = (-(1+q²)*(N/q)) mod q³
F  = F0+q³.
```

For these retained payloads, `0<C≤q` and `q | N`. Since `(q²-1)*(-(1+q²)) ≡ 1 (mod q³)`, this choice gives `R=A0-q(q²-1)F ≡ k-1 (mod q⁴)` and therefore `q⁴ | e` for `e=k-R-1`. Exact arithmetic also verifies `F≥q³`, negative R, `8P+4≤k`, and `2q⁴<c` where `c=kq³+1`. The source graph's Dtau and two steps of the first Pell recurrence are checked as exact sparse polynomial identities over `Z[q]`: for `B=2(P-1)+1`, `xcoord(2,B)=8P²+8P+1`, `ycoord(2,B)=4P+2`, `2*ycoord=k`, and Dtau is the square of that x-coordinate.

This is **not a full 74 graph zero**: second Pell/root and adjacent/carrier facts, the remaining witnesses, graph output and payload-to-symbolic-Lean binding are not verified. It does not refute a fixed-port guard theorem. It shows that the listed partial constraints, even together with `C≤q`, do not by themselves establish `F<q`. Other 74 graph factors could rule out this assignment.

Run `nice -n 15 python3 -I -S -B Computability/DiophantineConsistency/research/trace74-large-f-partial-obstruction/check.py` from the repository root. Author outer session 5874 exited 0 and was fully reaped; its inner receipt does not independently capture the outer exit. Checker SHA-256 `baa87502c789c4c0914cb3a145bd8d91cfbba412dc79aa945ec960b105751942`, stdout SHA-256 `f1589237da9a9ecb339344d6e3ccb8d91ffb977e9df7faaa2bdb836ffad94467`. The [independent scalar audit](../../reviews/trace74-large-f-partial-obstruction-independent/README.md) passed (SHA-256 `d57240cf69a9033b1b5f094097b4ba7d807170bbd16338afec333a5dd7927c91`), retaining the partial-graph and unverified second-Pell/carrier limitations.
