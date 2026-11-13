# A conditional constructive parent lift from two norms

Let ordinary nonnegative inputs and ports of the [nine-variable two-norm graph](../ordinary9-shifted-free-aux-two-norm64/README.md)
satisfy both actual residual equations \(A_0=A_1=0\), with \(\beta>0\).
Retain those inputs, the actual rank R, \(a=Y(X+1)\), \(A=a+2\),
\(\Delta=A^2-1\), and \(c=\eta+Yk>0\). Suppose the main Pell
ordinate has index m with

\[
c=y_m(A),\qquad m\equiv3\pmod4.
\]

Choose **any** positive index h for which \(c^2\mid y_h(A)\). If

\[
\gcd(4h,c)\mid R-m, \tag{†}
\]

then the original shifted-zeta 85-row **parent** has a natural zero with the
same first/main data. The auxiliary f, i, T, y inputs are constructed below;
y is an actual square root input, not an independent free square. This is a
standard-integer sufficient condition, not an unconditional reverse bridge,
a fixed-port zero construction, a proof of (†), or a Lean/iPRA result. It
does **not** assume \(m=R\).

A suitable h always exists: the Pell transition has determinant one modulo
\(c^2\), so some positive power is the identity. The substantive open
obligations are whether an appropriate h can satisfy (†) for the actual
two-norm witness, whether m can be arranged to be 3 modulo 4, or whether a
different construction can handle the other cases. The counterexample in the
[separate mod-31 packet](../ordinary13-shifted-free-aux-odd-index-31-obstruction/README.md)
shows that arbitrary chosen strong witnesses do not automatically work when
the actual main-root condition is omitted.

## Strong witness and an explicit matrix period

Write \((x_j,v_j)\) for the Pell pair of multiplier A, with
\((x_0,v_0)=(1,0)\). Set

\[
f=x_h,\quad v=v_h,\quad i=\Delta v/c^2,\quad I=c^2i=\Delta v.
\]

All are natural, f≥2 and i>0. The Pell norm gives
\(I^2=\Delta(f^2-1)\), the literal strong factor is 1, and
\(f^2\equiv1\pmod c\), so \(\gcd(f,c)=1\).

Let Q be the Pell transition matrix. Its hth power is
\(\begin{pmatrix}f&\Delta v\\v&f\end{pmatrix}\). Using the norm,

\[
Q^{2h}\equiv-\mathrm{Id}+
 2f\begin{pmatrix}0&\Delta v\\v&0\end{pmatrix}\pmod{f^2}.
\]

The binomial formula shows \(Q^{4hf}\equiv\mathrm{Id}\pmod{f^2}\).
Thus \(P=4hf\) is an explicit, possibly nonminimal period; no discrete
logarithm or construction of a minimal period is needed. Since f is coprime
to c, \(\gcd(P,c)=\gcd(4h,c)\). By (†), the Chinese remainder theorem
provides arbitrarily large L with

\[
L\equiv m\pmod P,\qquad L\equiv R\pmod c.
\]

Choose L≥m. As P is divisible by 4 and m≡3 modulo 4, L≡3 modulo 4.

## A square auxiliary witness

Let \((z_j,y_j)\) be the Pell sequence with multiplier I, and put
\(V=z_L/I\). Since L is odd, \(z_L\) is divisible by I, and
\(V>0\), \(y=y_L\) are natural. For \(L=2j+1\), define the integer
polynomial \(P_j(t)=z_{2j+1}(\sqrt t)/\sqrt t\). Its recurrence and
that of \(y_{2j+1}(A)\) give

\[
P_j(1-A^2)=(-1)^j y_{2j+1}(A),\qquad
P_j(0)=(-1)^j(2j+1).
\]

Here j is odd. Since \(I^2=\Delta(f^2-1)\),
\(I^2\equiv1-A^2\pmod{f^2}\); the explicit period and
\(L\equiv m\pmod P\) give \(y_L(A)\equiv y_m(A)=c\pmod{f^2}\).
Therefore \(V\equiv-c\pmod{f^2}\). Also \(I\equiv0\pmod c\), so
\(V\equiv-L\equiv-R\pmod c\). As \(f^2\equiv1\pmod c\), the
coprime moduli imply

\[
f^2c\mid V+c+f^2R,\qquad
T=\frac{V+c+f^2R}{f^2c}.
\]

For a two-norm zero with beta>0 and nonnegative ports, R>0. Indeed the
first norm excludes J=0; it also excludes C≤0 by comparing its signed root
with \(\beta J(\ell+k)\), since shifted k≥1. Thus
\(G=\alpha+(q-F)\beta J>0\), q≥2 and the nonnegative mask terms make
the actual rank R positive. Therefore T≥1. The parent inputs \(n_i=i-1\),
\(n_T=T-1\), \(n_f=f\), and \(n_y=y\) are natural. The equation for
T gives the actual auxiliary ordinate \(V=f^2(Tc-R)-c\), and its Pell
norm gives \(y^2-I^2(y^2-V^2)=1\). The first and main fields do not
use these four auxiliary inputs, so both remain zero and the parent output is
zero.

## Scope and checks

The open condition (†) depends only on the main ordinate, its index, the
actual rank, and a chosen positive modular Pell period; it does not use an
auxiliary zero or assume \(m=R\). The even stronger condition
\(c\mid R-m\) is immediately sufficient for (†), but is not asserted to
follow from the two norms. The \(m\not\equiv3\pmod4\) cases and possible
witness changes remain open.

The checker pins the two-norm and parent graphs, checks their exact shared
first/main expression trees and actual square/product rows, verifies the
explicit matrix period on bounded independent controls, and gives an exact
fact-level toy with \(A=2,c=15,m=3,h=90,R=18,L=3,T=2\). The toy
has \(m\ne R\) and checks the strong and square-auxiliary equations, but is
not asserted to be a graph zero. The displayed binomial and CRT proof is the
general argument; finite checks alone are not a proof. No giant Pell numbers,
Lean process, build, staging or model provider is used.

```sh
python3 -I -S -B research/ordinary13-shifted-two-norm-parent-crt-sufficient-condition/check.py | cmp - research/ordinary13-shifted-two-norm-parent-crt-sufficient-condition/receipt.json
```
