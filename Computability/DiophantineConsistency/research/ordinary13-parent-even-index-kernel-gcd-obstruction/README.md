# A weaker even-index same-data obstruction via the Pell kernel

Let standard natural first/main data of the shifted two-norm graph satisfy
both actual norm equations, with \(A\ge2\), \(c=y_m(A)>0\), and positive
**even** m. Write \(\Delta=A^2-1=d t^2\) with d>1 squarefree and t>0.
If

\[
\gcd(c^2,dt)\mid c, \tag{†}
\]

then no natural f, i, T, y inputs complete **those same first/main data** to
a zero of the shifted 85-row parent. The graph rank can be any integer, and
both signs of the auxiliary Pell root are excluded. This is a conditional
same-data result: it neither constructs a two-norm zero nor proves an
existential difference between the two equations. No Lean/model, iPRA or
Con(ZFC) theorem is claimed.

The hypothesis strictly weakens the [previous \(\gcd(m,\Delta)=1\) criterion](../ordinary13-parent-even-index-coprime-discriminant-obstruction/README.md).
It holds for every squarefree \(\Delta\) (t=1), and whenever
\(\gcd(m,t)=1\): the Pell transition modulo \(\Delta\) gives
\(\gcd(c,t)=\gcd(m,t)\), and the squarefree d then contributes at most
one copy of any prime of c. It also holds in cases with
\(\gcd(m,t)>1\). For example, the fact-level data
\(A=8,\Delta=63=7\cdot3^2,m=6,c=1032240\) have
\(\gcd(c^2,dt)=3\mid c\), while both \(\gcd(m,t)\) and
\(\gcd(m,\Delta)\) are 3. This is not asserted to be a graph zero.

## From the actual strong factor to the fundamental Pell subgroup

At a hypothetical same-data parent zero, both first/main factors are 1.
The strong and auxiliary factors must therefore be units; the literal
strong factor cannot be −1 modulo 4, as shown in the pinned previous packet.
Thus its actual fields satisfy

\[
I=c^2i>0,\quad i\ge1,\quad I^2=\Delta(f^2-1),\quad f\ge2,
\]

and the actual auxiliary factor must be 1. Prime valuations give
\(I=dt\,u\) for a positive integer u and
\(f^2-du^2=1\). Let \(\varepsilon\) be the least positive
**integer-coordinate norm-one Pell solution** for d, and let
\((X_j,U_j)\) be its nonnegative powers. Ordinary Pell classification gives
positive r,h with

\[
A+t\sqrt d=\varepsilon^r,\qquad
f+u\sqrt d=\varepsilon^h.
\]

This explicitly invokes the standard integer-coordinate Pell theorem, not an
arbitrary half-integral unit of a quadratic ring, and does not claim an iPRA
formalization. Let \(g_0=\gcd(c^2,dt)\). Since \(c^2\mid dt\,u\),
\(c^2/g_0\mid u\). Hypothesis (†) says \(g_0\mid c\), so
\(c\mid c^2/g_0\) and therefore \(c\mid U_h\). This is the only
place (†) is used.

Raising the main unit to m gives \(U_{rm}=t c\). The Pell addition
formula and \(\gcd(X_j,U_j)=1\) imply the strong-divisibility identity
\(\gcd(U_h,U_{rm})=U_{\gcd(h,rm)}\), as proved in the preceding packet.
Thus c divides \(U_g\), where \(g=\gcd(h,rm)\). If g were a proper
divisor of rm, then \(g\le rm/2\). Since m is even,

\[
c=\frac{2X_{rm/2}U_{rm/2}}t>U_{rm/2}\ge U_g,
\]

because \(X_{rm/2}\ge X_r=A>t\). This contradicts the positive
divisibility \(c\mid U_g\). Hence \(rm\mid h\). For
\(j=h/r\), j is a positive **even** multiple of m and
\(f=x_j(A)\). The strong equation itself then forces
\(I=\Delta y_j(A)\), using positive square roots; it is **not** necessary
to assert \(c^2\mid y_j(A)\).

## The even-subgroup anti-diagonal obstruction

The doubling identity makes \(f=x_j(A)>1\) odd, so choose any odd prime
p dividing f. Modulo p the A-Pell transition to the even index j is an
invertible anti-diagonal matrix. No odd-index A-Pell ordinate can vanish
modulo p: if \(y_u\equiv0\) for odd u, its transition would be a scalar
\(\pm\mathrm{Id}\), contradicting the fact that the odd power of the
invertible anti-diagonal \(Q^j\) is still anti-diagonal. For any odd
auxiliary Pell index \(\ell\), both \(\ell-m\) and \(\ell+m\) are
odd. The exact addition identity

\[
y_\ell(A)^2-y_m(A)^2=y_{\ell-m}(A)y_{\ell+m}(A)
\]

therefore gives \(y_\ell(A)\not\equiv\pm c\pmod p\).

However the literal auxiliary factor equation, via standard Pell
classification and either root sign, requires
\(V=\pm x_\ell(I)/I\) for an odd index \(\ell\), and its actual
ordinate formula \(V=f^2(Tc-R)-c\) gives
\(V\equiv-c\pmod{f^2}\). Since
\(I^2=\Delta(f^2-1)\equiv1-A^2\pmod{f^2}\), the exact odd-quotient
polynomial identity makes that congruence force
\(y_\ell(A)\equiv\pm c\pmod p\), a contradiction. This argument
applies regardless of R and T and does not assume \(m=R\).

## Reproduction and boundaries

The checker pins and reproduces the previous all-discriminants source packet,
checks actual parent factor rows, runs bounded kernel-cancellation, Pell and
anti-diagonal controls, and records strict illustrative cases beyond the
old hypotheses. In particular, the independently identified fact-level case
\(A=2,m=6,c=780,j=1560\) has
\(y_j\equiv202800\not\equiv0\pmod{c^2}\), while
\(\Delta y_j\equiv0\pmod{c^2}\). It demonstrates why the proof must use
the underlying even-subgroup anti-diagonal argument rather than assert
\(c^2\mid y_j\). These controls are not graph zeros. The displayed integer
classification, divisibility, growth and anti-diagonal proof gives the
conditional theorem; finite tests do not. In particular, the conditions are
not claimed to hold for an actual compact two-norm zero. No Lean, build,
staging, model provider, or giant Pell expansion is used.

```sh
python3 -I -S -B research/ordinary13-parent-even-index-kernel-gcd-obstruction/check.py | cmp - research/ordinary13-parent-even-index-kernel-gcd-obstruction/receipt.json
```
