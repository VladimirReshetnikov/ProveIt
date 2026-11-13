# Main norm forces k>q in the eta/zeta parent

For the exact 85-row eta/zeta parent, and also the 84-row F and alpha shift probes that preserve its main expression, suppose all witness coordinates are ordinary natural numbers, q≥2, and the **main residual itself is zero**. Then `k>q`. This statement does not require the first norm, compact mask bounds, or any assumption on F or alpha. It does not by itself extract the main residual from a full product zero, establish a reverse zero map, or prove an arithmetic-model or Lean theorem.

Write

```text
X=q*w,  Y=q³*s,  k=eta+n_zeta+1,
a=Y*(X+1),  A=a+2,  c=Y*k+eta,
U=Y*q²,  Delta=A²−1.
```

Here s≥1, Y≥q³≥8, X≥0, `0≤eta≤k−1`, and U>0. The zero main residual says `Dstar²=U²*(1+Delta*c²)`. By standard integer square divisibility, `U | Dstar`, so there is a nonnegative integer d with

```text
d²−(A²−1)c²=1.                         (1)
```

Suppose `1≤k≤q`. Then `1<c≤qY+q−1≤Y²+Y−1`.

If w>0, then X≥q and `1<c<2A`, because `a≥Y*(q+1)`. There is no solution of (1) in that interval: the radicand lies strictly between `(Ac−1)²` and `(Ac)²`.

If w=0, then X=0 and A=Y+2. For k=1 or 2, the same first square gap applies: `1<c<2A`. For k≥3, `2A<c`, since `c≥3Y>2Y+4`; also `c<2A²`, since `c≤Y²+Y−1<2(Y+2)²`. The following elementary descent rules out this interval:

* For `A≥2`, `c>1` satisfying (1), the norm lies strictly below `(Ac)²` and above `((A−1)c)²`; therefore `t=Ac−d` is a positive integer with t<c.
* Put `d′=A*d−(A²−1)*c`. It is positive because `(A*d)²−((A²−1)c)²=A²+(A²−1)c²>0`. Direct identities give `d′²−(A²−1)t²=1` and `c=d′+A*t`.
* If c<2A² then `t<2A`. The first square gap excludes `1<t<2A`, so t=1. Its norm gives d′=A, and then `c=2A`, contrary to c>2A.

Thus neither w case permits k≤q. The derivation also works when eta=0, and does not assume positive eta or a particular Pell index. In the F-unshift investigation it narrows the unresolved F=0, C>0 branch to k>q; it does not exclude that branch.

The checker pins both exact graph sources and the previous square-gap receipt, verifies the inverse-Pell polynomial identities, and tests bounded natural coordinates with `1≤k≤q`. These tests do not replace the universal descent argument above. No Lean, build, provider or model validation was run.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-eta85-main-ordinate-q-bound/check.py | cmp - research/ordinary13-eta85-main-ordinate-q-bound/receipt.json
```
