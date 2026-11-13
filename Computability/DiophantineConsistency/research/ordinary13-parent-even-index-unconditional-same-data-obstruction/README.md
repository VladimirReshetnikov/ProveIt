# Even main index: unconditional same-data parent obstruction

Let standard natural first/main data of the shifted two-norm graph satisfy
both actual norm equations. Suppose their main multiplier is \(A\ge2\)
and their positive main ordinate is \(c=y_m(A)\) at a **positive even**
Pell index m. Then **no** natural f, i, T, y inputs complete those same
first/main data to a zero of the shifted 85-row parent. The result needs no
squarefreeness or gcd condition on \(\Delta=A^2-1\), and no assumption
about the rank R or the sign of either auxiliary root.

This is an unconditional statement only about **same-data completion at an
even index**. It does not construct a two-norm zero, exclude a different
first/main witness with odd index, prove that the parent and two-norm
equations have different existential zero status, or establish a Lean,
model, iPRA or Con(ZFC) theorem.

The proof strengthens the [kernel-gcd conditional theorem](../ordinary13-parent-even-index-kernel-gcd-obstruction/README.md).
The uniform cancellation and growth argument below was independently suggested
and checked during the audit. Notably, this obstruction uses only the weaker
fact \(c\mid I\); the actual graph supplies \(I=c^2i\).

## Strong factor and fundamental Pell coordinates

At a hypothetical parent completion the two unchanged first/main factors
are 1. The remaining factors are integer units, and the actual strong factor
cannot be −1 modulo 4, as established in the pinned kernel-gcd packet. Thus
its literal fields satisfy

\[
I=c^2i>0,\quad i\ge1,\quad I^2=\Delta(f^2-1),\quad f\ge2.
\]

Write \(\Delta=d t^2\), with d>1 squarefree and t>0. Prime valuations
give \(I=dt\,u\) for a positive integer u, and hence
\(f^2-du^2=1\). Use the standard classification of **integer-coordinate
norm-one Pell solutions**: for the least positive such unit
\(\varepsilon=a+b\sqrt d\), its powers have coordinates \((X_j,U_j)\),
and positive integers r,h satisfy

\[
A+t\sqrt d=\varepsilon^r,\qquad
f+u\sqrt d=\varepsilon^h.
\]

This invokes ordinary integer Pell classification, not an arbitrary
half-integral unit of the full quadratic ring. It is a stated mathematical
input, not an iPRA formalization or Lean replay.

## A uniform divisibility and growth argument

Let \(D_0=\gcd(c,dt)\). The main Pell transition modulo
\(\Delta\) gives \(c=y_m(A)\equiv mA^{m-1}\pmod\Delta\).
Since \(dt\mid\Delta\) and \(\gcd(A,\Delta)=1\),

\[
D_0=\gcd(m,dt)\le m. \tag{1}
\]

From \(c\mid I=dt\,U_h\), ordinary gcd cancellation gives
\(c/D_0\mid U_h\). The main unit raised to m gives
\(U_{rm}=tc\), so \(c/D_0\) also divides \(U_{rm}\). Pell strong
divisibility,

\[
\gcd(U_h,U_{rm})=U_{\gcd(h,rm)},
\]

follows from the addition formula and \(\gcd(X_j,U_j)=1\), as proved
in the pinned predecessor. If \(g=\gcd(h,rm)\) were a proper divisor,
then \(g\le rm/2\) and the positive increasing ordinates give

\[
\frac c{D_0}\le U_g\le U_{rm/2}. \tag{2}
\]

But Pell doubling yields \(tc=2X_{rm/2}U_{rm/2}\), and
\(X_{rm/2}=x_{m/2}(A)\). For every \(j\ge1\),
\(x_j(A)\ge jA\): the first value is A and each step is at least twice
the previous x-coordinate. Since \(A>t\) from \(A^2-dt^2=1\),
(1) gives

\[
2X_{rm/2}\ge mA>mt\ge D_0t,
\quad\text{so}\quad \frac c{D_0}>U_{rm/2},
\]

contradicting (2). This includes m=2 without a separate case. Hence
\(rm\mid h\). For \(j=h/r\), j is a positive even multiple of m and
\(f=X_h=x_j(A)\). The argument does **not** need to conclude
\(c^2\mid y_j(A)\).

## Both auxiliary signs are impossible

The even-index doubling identity makes \(f=x_j(A)>1\) odd. Choose an odd
prime p dividing f. The A-Pell transition \(Q^j\) modulo p is invertible
and anti-diagonal. If any odd A-Pell ordinate \(y_u(A)\) vanished modulo p,
then \(Q^u=\pm\mathrm{Id}\), but \((Q^j)^u\) would be invertible
anti-diagonal, a contradiction. Thus both odd indices \(\ell-m\) and
\(\ell+m\) have nonzero ordinates modulo p for every odd \(\ell\).
The exact addition identity gives

\[
y_\ell(A)^2-c^2=y_{\ell-m}(A)y_{\ell+m}(A)\not\equiv0\pmod p.
\]

On the other hand, the actual auxiliary factor-one equation and ordinary
Pell classification give an odd \(\ell=2j'+1\) and either sign of
\(V=x_\ell(I)/I\). The graph ordinate formula
\(V=f^2(Tc-R)-c\) forces \(V\equiv-c\pmod{f^2}\). The exact
odd-quotient identity, using
\(I^2\equiv1-A^2\pmod{f^2}\), would then force
\(y_\ell(A)\equiv\pm c\pmod p\), a contradiction. The auxiliary
sign, R, T, and all possible strong witnesses are covered.

## Reproduction and proof boundaries

The checker pins and reproduces the previous kernel-gcd packet, checks the
uniform cancellation/growth inequalities and runs bounded exact
fundamental-unit and strong-index controls. These include both cases inside
and outside the earlier kernel-gcd criterion. The proof above uses the stated
standard Pell classification, Euclidean strong divisibility, and elementary
integer arithmetic; finite controls alone do not prove it. The graph factor
and odd-quotient bindings are inherited from the pinned, separately reviewed
predecessors. No Lean, build, staging, provider audit, huge Pell expansion,
or model theorem is used.

```sh
python3 -I -S -B research/ordinary13-parent-even-index-unconditional-same-data-obstruction/check.py | cmp - research/ordinary13-parent-even-index-unconditional-same-data-obstruction/receipt.json
```
