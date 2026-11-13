# Independent review: two-norm positivity transfer

The [reviewed transfer](../../research/ordinary13-free-aux-square-two-norm-positive-k-transfer/README.md)
validly gives \(k=\eta+\zeta>0\), and hence \(c=\eta+Yk>0\), at
an ordinary natural full zero of the free auxiliary-square graph under the
stated nonnegative port assumptions
\(\beta>0\), \(K_0>0\), \(MC<\beta\), \(MF<2\beta\).
The fixed symbolic compact tuple satisfies those assumptions. This removes
c=0 in the earlier compact positive-index boundary, while that boundary's
index estimate remains restricted to its own \(J=1,w=s=1\) slice.
No Lean/model endpoint or zero-preserving map is established.

The independent checker builds ordered expression trees from the two exact
84-row JSON graphs. In the independent-k graph it substitutes the expression
\(\eta+\zeta\) for its input \(k\), and verifies equality with the
free-square graph for both residuals and all relevant rank, root and parameter
fields. It preserves operand order and integer subtraction, compares all
witness and port positions, and does not substitute or use the free square
input in either residual. This is a literal expression identity, not an
assertion that the graphs have equivalent zeros or that every independent-k
zero satisfies \(k\ge\eta\).

At a full output zero all integer factors are ±1. For the first factor, write
\(b=J\beta\) and \(q=1+b\). If b is even its negative square term is 0
modulo 4; if b is odd q is even, so \(Y=q^3s\) and
\(\ell=XY^2k\) are divisible by 4. In both cases the first factor cannot
be −1 modulo 4. For the main factor, \(\Delta=a^2+4a+3\) is 0 or 3
modulo 4, so \(1+\Delta c^2\) is 0 or 1; its factor is never −1
modulo 4 either. Both factors therefore equal +1 and A0=A1=0.

The inherited [two-norm theorem](../../research/ordinary13-independent-k-two-norm-kpositive-audit/README.md)
uses precisely the stated natural-input and port inequalities. At k=0 its
first norm treats the C>0 branch and the C≤0 signed-root exception, proving
for the actual graph rank \(0<R+1<q^4\). Its main norm gives
\(q^5\mid H(R+1)\), with \(H=3+4a\) and \(q^3\mid a\).
The gcd of H and \(q^5\) is 1 or 3; if it is 3, then 3 divides q.
Thus \(q^4\mid R+1\), contradicting the rank bounds. In particular, this
argument does not cancel 3 when it is not a unit modulo q, and uses neither
auxiliary squarehood nor a first-index bound. The earlier independent review
of that arithmetic is [here](../ordinary13-independent-k-two-norm-kpositive-independent/README.md).

For the exact compact tuple, the fixed beta is positive; the source-defined
kernel is positive; the low mask has a strict digit deficit from beta; and
the high-mask top digit is zero, so its value is below beta and
\(MF=\beta+\mathrm{highNat}<2\beta\). These are ordinary integer
consequences of the pinned coefficient recipes, not a Lean provider replay.

The checker independently compares 19 exact trees, exhausts 1,024 first and
256 main mod-4 cases, and checks the relevant fixed recipe declarations. The
author's receipt also reproduces. No Lean, build, staging, model-provider
validation or iPRA proof was performed.

```sh
python3 -I -S -B reviews/ordinary13-free-aux-square-two-norm-positive-k-transfer-independent/check.py | cmp - reviews/ordinary13-free-aux-square-two-norm-positive-k-transfer-independent/receipt.json
```
