# Signed main-root obstruction for early main Pell indices

This extends the separate [y₃ signed-root obstruction](../ordinary13-free-aux-square-y3-signed-main-obstruction/README.md). In the fixed-compact free auxiliary-square candidate, restrict to `X=q`, `s=1`, and let `c=ycoord(m,a)` for a natural **standard** Pell index `1≤m<N`, where `N=67*8807` and q=2^N. The actual main residual cannot vanish. Consequently, by the independently checked main-factor unit argument, no complete ordinary-integer product zero occurs in this restricted slice. Other X, s or main indices remain open; this is not a global no-zero or Lean/model theorem.

Put `a=q³(q+1)`, `A=a+2`, `Delta=A²−1`, `H=4a+3`, `U=q⁵`, and `(g_m,c_m)=Pell(A,m)`. The elementary Pell step gives

```
g_m−a*c_m ≡ 2^m (mod H),
(g_m−a*c_m)(g_m+a*c_m) ≡ 1 (mod H).
```

For the exact child root `Dstar=U(q+a*c_m)+H(U*gamma+R+1−k)`, a vanishing main residual yields U|Dstar. Since H is odd and U is a power of two, U also divides `R+1−k`. Therefore `d=Dstar/U` is an integer with `d−a*c_m≡q (mod H)` and `d²=g_m²`, so d=±g_m.

For the positive sign, `H | 2^m−q`; when m<N this difference is nonzero with absolute value below q<H. For the negative sign, multiply the conjugate relation by 2^m: `H | q*2^m+1`. Here `0<q*2^m+1<q²+1<H`. Both are impossible. The sign argument does not require first-norm, rank-representation, eta, alpha, or auxiliary hypotheses.

At m=N, the positive-sign divisibility becomes automatic and this size argument no longer excludes it; the negative sign is still impossible because `q²+1<H`. The packet makes no claim about m>N or about a main ordinate not supplied with such an index. Its `Pell` recurrence is ordinary integer arithmetic; source files are pinned only for comparison and no nonstandard-model interpretation or Lean elaboration is claimed.

The checker reproduces the y₃ predecessor receipt, verifies the Pell norm and congruence-step identities as exact integer polynomials, and checks bounded N/m controls without constructing the fixed compact q or its Pell coordinates. The symbolic argument above, not those finite controls, proves the stated early-index bound. No Lean, provider/axiom replay, global equivalence or PDF binding was performed. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-free-aux-square-early-main-index-obstruction/check.py | cmp - research/ordinary13-free-aux-square-early-main-index-obstruction/receipt.json
```
