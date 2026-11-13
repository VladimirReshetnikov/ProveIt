# Even-index same-data obstruction without squarefree discriminant

Let standard natural first/main data of the shifted two-norm graph have
\(A\ge2\), main ordinate \(c=y_m(A)>0\), and a **positive even** main
Pell index m. Put \(\Delta=A^2-1\). If

\[
\gcd(m,\Delta)=1, \tag{†}
\]

then no choice of the parent's f, i, T, y auxiliary inputs can complete
**those same** first/main data to a zero of the shifted 85-row parent. There
is **no squarefreeness assumption on** \(\Delta\). This strengthens the
[separate squarefree corollary](../ordinary13-parent-even-index-squarefree-same-data-obstruction/README.md).

The theorem is conditional. It does not prove that any two-norm witness with
(†) exists, that such a witness occurs at the exact compact tuple, that the
parent has no different witness, or that the two equations differ in
existential zero status. It is standard-integer mathematics, not a checked
Lean/model or iPRA/Con(ZFC) result.

## Reduction to a fundamental Pell unit

As in the squarefree packet, a hypothetical same-data parent completion must
make its strong and auxiliary factors +1: its first/main factors are already
1, their product with the auxiliary factors is 1, and the literal strong
factor cannot be −1 modulo 4. Write its actual positive graph fields as

\[
I=c^2i>0,\quad i\ge1,\quad
I^2=\Delta(f^2-1),\quad f\ge2.
\]

Write \(\Delta=d t^2\), with d>1 squarefree and t>0. Such a d exists
and exceeds 1 because \(A^2-1\) lies strictly between consecutive
squares. Prime valuations of \(\Delta\mid I^2\) show
\(dt\mid I\). Put \(u=I/(dt)>0\); then

\[
f^2-d u^2=1,\qquad c^2\mid dt\,u. \tag{1}
\]

Use the standard **integer** fundamental-unit classification of the
norm-one Pell equation: among solutions with **integer coordinates** and
positive ordinate there is a least solution \(\varepsilon=a+b\sqrt d>1\);
every such solution is a nonnegative integer power of it, and those powers
have natural integer coordinates
\((X_j,U_j)\). Thus for positive integers r,h,

\[
A+t\sqrt d=\varepsilon^r,\qquad
f+u\sqrt d=\varepsilon^h. \tag{2}
\]

This generator is for integer-coordinate norm-one Pell solutions; it is not
an arbitrary unit of the full quadratic ring of integers, which may contain
half-integral coordinates. This ordinary Pell classification is an explicit mathematical input; the
packet does not claim that a general squarefree-kernel classification has
been formalized in iPRA or compiled in Lean.

As in the previous packet,
\(\gcd(c,\Delta)=\gcd(m,\Delta)=1\): modulo \(\Delta\), the main
transition matrix gives \(y_m(A)\equiv mA^{m-1}\), and A is a unit
modulo \(\Delta\). Hence \(\gcd(c,dt)=1\), and (1) implies
\(c^2\mid u=U_h\). In particular \(c\mid U_h\). Raising the first
equality in (2) to m gives

\[
U_{rm}=t\,c. \tag{3}
\]

## Pell strong divisibility forces the same subgroup

For the coordinates of **one** fixed norm-one Pell unit,

\[
\gcd(U_i,U_j)=U_{\gcd(i,j)}\quad(i,j\ge0). \tag{4}
\]

For completeness, the addition formula is
\(U_{j+k}=U_jX_k+X_jU_k\). The norm gives
\(\gcd(X_j,U_j)=1\), so
\(\gcd(U_j,U_{j+k})=\gcd(U_j,U_k)\); the Euclidean algorithm proves
(4), including \(U_0=0\). This is an ordinary integer theorem and needs
no unverified provider assumption in the argument here.

Because c divides both \(U_h\) and \(U_{rm}=tc\), (4) gives
\(c\mid U_g\) for \(g=\gcd(h,rm)>0\). If g were a proper divisor of
rm, then \(g\le rm/2\). The evenness of m and the doubling identity
would imply

\[
c=\frac{2X_{rm/2}U_{rm/2}}t>U_{rm/2}\ge U_g,
\]

contradicting \(c\mid U_g\). The inequality is strict even at m=2:
\(rm/2\ge r\), the positive x-coordinates increase, and
\(X_{rm/2}\ge X_r=A>t\) because \(A^2-dt^2=1\), d>1.
Therefore \(rm\mid h\).

Set \(j=h/r\). From (2), \(f=x_j(A)\) and
\(U_h=t\,y_j(A)\). Since \(c^2\mid U_h\) and \(\gcd(c,t)=1\),
\(c^2\mid y_j(A)\). Thus **every** possible strong witness has the
exact form excluded by the [reviewed even-main-index Pell obstruction](../ordinary13-parent-even-main-strong-pell-obstruction/README.md).
That obstruction rules out both signs and every odd auxiliary index for any
rank R or T, so the required auxiliary factor cannot be one. This proves the
same-data claim.

## Reproduction and scope

The checker pins and reproduces the previous squarefree and even-family
packets, tests the squarefree-kernel valuation implication and Pell ordinate
gcd identity in bounded exact arithmetic, and checks a non-squarefree,
nonfundamental-multiplier illustration:

\[
A=2024,\quad \Delta=4096575=7\cdot765^2,\quad
8+3\sqrt7\text{ has }r=3,\quad m=2,\quad c=4048.
\]

It verifies \(U_6=765c\), the strict m=2 growth comparison, and an explicit
modular strong-index control without expanding its large Pell witness. This
illustration is not claimed to satisfy the graph's two norms or fixed ports.
The fundamental-unit classification, valuation, Euclidean and growth proof
above establish the conditional theorem; finite controls do not. No Lean,
build, staging, model provider or giant Pell expansion is used.

```sh
python3 -I -S -B research/ordinary13-parent-even-index-coprime-discriminant-obstruction/check.py | cmp - research/ordinary13-parent-even-index-coprime-discriminant-obstruction/receipt.json
```
