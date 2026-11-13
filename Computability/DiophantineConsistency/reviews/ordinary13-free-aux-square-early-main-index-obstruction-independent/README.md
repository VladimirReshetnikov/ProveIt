# Independent review: early signed main-Pell indices

The [reviewed packet](../../research/ordinary13-free-aux-square-early-main-index-obstruction/README.md)
correctly excludes full ordinary-integer graph zeros in its stated fixed-port
slice: \(q=2^N\), \(N=590069\), \(X=q\), \(s=1\), and
\(c=y_m\) for a supplied standard Pell index \(1\le m<N\). It does not
exclude other X, s or indices, and the positive-root case at m=N remains
open. The fixed tuple's literal \(q=1+\beta J\) implies J=1 in this slice.

The literal candidate rows give \(Y=q^3\), \(U=q^5\),
\(a=q^3(q+1)\), \(H=4a+3\), and
\(D_*=U(q+ac)+H(U\gamma+R+1-k)\). The pinned Pell source uses parameter a,
so its multiplier is \(A=a+2\) and its norm discriminant is
\(\Delta=A^2-1=a^2+H\).

If the actual main residual vanishes, \(U^2\mid D_*^2\) gives
\(U\mid D_*\). Since H is odd, \(\gcd(H,U)=1\), hence
\(U\mid R+1-k\). The signed integer \(d=D_*/U\) therefore obeys
\(d-ac\equiv q\pmod H\). The norm and \(c=y_m\) imply
\(d=\pm x_m\); neither sign is discarded.

The Pell recurrence gives
\(x_m-ay_m\equiv2^m\pmod H\), and its norm gives
\((x_m-ay_m)(x_m+ay_m)\equiv1\pmod H\). With the positive sign,
the literal-root congruence would require \(H\mid2^m-q\). For m<N,
\(0<q-2^m<q<H\), impossible. With the negative sign, multiplying by
\(2^m\) requires \(H\mid q2^m+1\). For m≤N,
\(0<q2^m+1\le q^2+1<H\), also impossible. At m=N the positive
congruence becomes automatic; this establishes no full zero there.

The output is a product of four integer factors minus one. At output zero,
the main factor is ±1. Independently checking the actual
\(\Delta=a^2+4a+3\) modulo 4 gives
\(1+\Delta c^2\equiv0\) or 1; hence the main factor
\(1+D_*^2-U^2(1+\Delta c^2)\) cannot be −1 modulo 4. It must be
+1, which forces the main residual to vanish and triggers the signed-root
contradiction. No auxiliary-factor or first-root hypothesis is needed.

The checker pins and checks the relevant source, all graph root/output rows,
256 mod-4 cases, signed congruence controls and both modulus-size bounds,
including the negative sign at m=N. These bounded controls do not replace
the uniform argument above. The author receipt reproduces. No Lean, build,
staging, all-model theorem or iPRA result was performed or claimed.

```sh
python3 -I -S -B reviews/ordinary13-free-aux-square-early-main-index-obstruction-independent/check.py | cmp - reviews/ordinary13-free-aux-square-early-main-index-obstruction-independent/receipt.json
```
